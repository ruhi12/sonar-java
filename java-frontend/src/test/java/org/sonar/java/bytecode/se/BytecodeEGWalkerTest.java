/*
 * SonarQube Java
 * Copyright (C) 2012-2017 SonarSource SA
 * mailto:info AT sonarsource DOT com
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 3 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */
package org.sonar.java.bytecode.se;

import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import java.io.File;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.function.BiConsumer;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.junit.BeforeClass;
import org.junit.Rule;
import org.junit.Test;
import org.sonar.api.utils.log.LogTester;
import org.sonar.api.utils.log.LoggerLevel;
import org.sonar.java.ast.parser.JavaParser;
import org.sonar.java.bytecode.loader.SquidClassLoader;
import org.sonar.java.bytecode.se.testdata.BytecodeTestClass;
import org.sonar.java.bytecode.se.testdata.ExceptionEnqueue;
import org.sonar.java.bytecode.se.testdata.FinalBytecodeTestClass;
import org.sonar.java.bytecode.se.testdata.MaxRelationBytecode;
import org.sonar.java.resolve.SemanticModel;
import org.sonar.java.se.ProgramState;
import org.sonar.java.se.SETestUtils;
import org.sonar.java.se.SymbolicExecutionVisitor;
import org.sonar.java.se.checks.DivisionByZeroCheck;
import org.sonar.java.se.checks.InvariantReturnCheck;
import org.sonar.java.se.constraint.BooleanConstraint;
import org.sonar.java.se.constraint.Constraint;
import org.sonar.java.se.constraint.ObjectConstraint;
import org.sonar.java.se.symbolicvalues.SymbolicValue;
import org.sonar.java.se.xproc.BehaviorCache;
import org.sonar.java.se.xproc.ExceptionalYield;
import org.sonar.java.se.xproc.HappyPathYield;
import org.sonar.java.se.xproc.MethodBehavior;
import org.sonar.java.se.xproc.MethodYield;
import org.sonar.plugins.java.api.semantic.Type;
import org.sonar.plugins.java.api.tree.CompilationUnitTree;

import static org.fest.assertions.Assertions.assertThat;

public class BytecodeEGWalkerTest {

  private static SquidClassLoader squidClassLoader;
  @Rule
  public LogTester logTester = new LogTester();

  private static SemanticModel semanticModel;

  @BeforeClass
  public static void setUp() throws Exception {
    squidClassLoader = new SquidClassLoader(Lists.newArrayList(new File("target/test-classes"), new File("target/classes")));
    semanticModel = SemanticModel.createFor((CompilationUnitTree) JavaParser.createParser().parse("class A {}"), squidClassLoader);
  }

  @Test
  public void generateMethodBehavior() throws Exception {
    MethodBehavior methodBehavior = getMethodBehavior("fun(ZLjava/lang/Object;)Ljava/lang/Object;");
    assertThat(methodBehavior.yields()).hasSize(2);

    SymbolicValue svFirstArg = new SymbolicValue();
    SymbolicValue svsecondArg = new SymbolicValue();
    SymbolicValue svResult = new SymbolicValue();
    List<SymbolicValue> invocationArguments = Lists.newArrayList(svFirstArg, svsecondArg);
    List<ObjectConstraint> collect = methodBehavior.yields().stream().map(my -> {

      Collection<ProgramState> ps = my.statesAfterInvocation(invocationArguments, Lists.newArrayList(), ProgramState.EMPTY_STATE, () -> svResult).collect(Collectors.toList());
      assertThat(ps).hasSize(1);
      ProgramState next = ps.iterator().next();
      return next.getConstraint(svResult, ObjectConstraint.class);
    })
      .collect(Collectors.toList());
    assertThat(collect).hasSize(2).containsOnly(ObjectConstraint.NOT_NULL, ObjectConstraint.NULL);

    List<HappyPathYield> nullConstraintOnResult =
      methodBehavior.happyPathYields().filter(my -> ObjectConstraint.NULL.equals(my.resultConstraint().get(ObjectConstraint.class))).collect(Collectors.toList());
    assertThat(nullConstraintOnResult).hasSize(1);
    HappyPathYield nullConstraintResult = nullConstraintOnResult.get(0);
    Collection<ProgramState> ps = nullConstraintResult.statesAfterInvocation(invocationArguments, Lists.newArrayList(), ProgramState.EMPTY_STATE, () -> svResult).collect(Collectors.toList());
    assertThat(ps).hasSize(1);
    ObjectConstraint constraint = ps.iterator().next().getConstraint(svsecondArg, ObjectConstraint.class);
    assertThat(constraint).isSameAs(ObjectConstraint.NULL);
  }

  @Test
  public void verify_behavior_of_fun2_method() throws Exception {
    MethodBehavior methodBehavior = getMethodBehavior("fun2(Z)Ljava/lang/Object;");
    assertThat(methodBehavior.yields()).hasSize(2);

    SymbolicValue svFirstArg = new SymbolicValue();
    SymbolicValue svResult = new SymbolicValue();
    List<SymbolicValue> invocationArguments = Lists.newArrayList(svFirstArg);
    List<HappyPathYield> oneYield =
      methodBehavior.happyPathYields().filter(my -> ObjectConstraint.NULL.equals(my.resultConstraint().get(ObjectConstraint.class))).collect(Collectors.toList());

    assertThat(oneYield).hasSize(1);
    HappyPathYield yield = oneYield.get(0);
    Collection<ProgramState> pss = yield.statesAfterInvocation(invocationArguments, Lists.newArrayList(), ProgramState.EMPTY_STATE, () -> svResult).collect(Collectors.toList());
    assertThat(pss).hasSize(1);
    ProgramState ps = pss.iterator().next();
    assertThat(ps.getConstraint(svFirstArg, ObjectConstraint.class)).isNull();
    assertThat(ps.getConstraint(svFirstArg, BooleanConstraint.class)).isSameAs(BooleanConstraint.TRUE);
    assertThat(ps.getConstraint(svFirstArg, DivisionByZeroCheck.ZeroConstraint.class)).isNull();

    oneYield =
      methodBehavior.happyPathYields().filter(my -> ObjectConstraint.NOT_NULL.equals(my.resultConstraint().get(ObjectConstraint.class))).collect(Collectors.toList());

    assertThat(oneYield).hasSize(1);
    yield = oneYield.get(0);
    pss = yield.statesAfterInvocation(invocationArguments, Lists.newArrayList(), ProgramState.EMPTY_STATE, () -> svResult).collect(Collectors.toList());
    assertThat(pss).hasSize(1);
    ps = pss.iterator().next();
    assertThat(ps.getConstraint(svFirstArg, ObjectConstraint.class)).isNull();
    assertThat(ps.getConstraint(svFirstArg, BooleanConstraint.class)).isSameAs(BooleanConstraint.FALSE);
    assertThat(ps.getConstraint(svFirstArg, DivisionByZeroCheck.ZeroConstraint.class)).isNull();

  }

  @Test
  public void test_int_comparator() throws Exception {
    MethodBehavior methodBehavior = getMethodBehavior("int_comparison(II)Ljava/lang/Object;");
    assertThat(methodBehavior.yields()).hasSize(1);
    HappyPathYield methodYield = ((HappyPathYield) methodBehavior.yields().get(0));
    assertThat(methodYield.resultConstraint().get(ObjectConstraint.class)).isSameAs(ObjectConstraint.NULL);
  }

  @Test
  public void goto_terminator() throws Exception {
    MethodBehavior methodBehavior = getMethodBehavior("gotoTerminator(Ljava/lang/Object;)Z");
    assertThat(methodBehavior.yields()).hasSize(2);
  }

  @Test
  public void test_method_throwing_exception() throws Exception {
    MethodBehavior methodBehavior = getMethodBehavior("throw_exception()V");
    assertThat(methodBehavior.yields()).hasSize(1);
    MethodYield methodYield = methodBehavior.yields().get(0);
    assertThat(methodYield).isInstanceOf(ExceptionalYield.class);
  }

  @Test
  public void test_method_is_complete() {
    String desc = "(Ljava/lang/String;)Z";
    MethodBehavior nativeMethod = getMethodBehavior("nativeMethod" + desc);
    assertThat(nativeMethod.isComplete()).isFalse();

    MethodBehavior abstractMethod = getMethodBehavior("abstractMethod" + desc);
    assertThat(abstractMethod.isComplete()).isFalse();

    MethodBehavior finalMethod = getMethodBehavior("finalMethod" + desc);
    assertThat(finalMethod.isComplete()).isFalse();

    MethodBehavior staticMethod = getMethodBehavior("staticMethod" + desc);
    assertThat(staticMethod.isComplete()).isTrue();

    MethodBehavior privateMethod = getMethodBehavior("privateMethod" + desc);
    assertThat(privateMethod.isComplete()).isFalse();

    MethodBehavior publicMethodInFinalClass = getMethodBehavior(FinalBytecodeTestClass.class, "publicMethod" + desc);
    assertThat(publicMethodInFinalClass.isComplete()).isFalse();
  }

  @Test
  public void method_array() throws Exception {
    BytecodeEGWalker walker = getBytecodeEGWalker(squidClassLoader);
    MethodBehavior behavior = walker.getMethodBehavior("java.lang.Class[]#clone()Ljava/lang/Object;", squidClassLoader);
    assertThat(behavior).isNull();
  }

  @Test
  public void test_starting_states() throws Exception {
    BytecodeEGWalker walker = new BytecodeEGWalker(null, semanticModel);

    String signature = "type#foo()V";
    walker.methodBehavior = new MethodBehavior(signature);
    ProgramState startingState = Iterables.getOnlyElement(walker.startingStates(signature, ProgramState.EMPTY_STATE, false));
    SymbolicValue thisSv = startingState.getValue(0);
    assertThat(thisSv).isNotNull();
    assertThat(startingState.getConstraints(thisSv).get(ObjectConstraint.class)).isEqualTo(ObjectConstraint.NOT_NULL);

    startingState = Iterables.getOnlyElement(walker.startingStates(signature, ProgramState.EMPTY_STATE, true));
    assertThat(startingState).isEqualTo(ProgramState.EMPTY_STATE);

    signature = "type#foo(DIJ)V";
    walker.methodBehavior = new MethodBehavior(signature);
    startingState = Iterables.getOnlyElement(walker.startingStates(signature, ProgramState.EMPTY_STATE, true));
    assertThat(startingState.getValue(0)).isNotNull();
    SymbolicValue doubleArg = startingState.getValue(0);
    assertThat(startingState.getConstraint(doubleArg, BytecodeEGWalker.StackValueCategoryConstraint.class)).isEqualTo(BytecodeEGWalker.StackValueCategoryConstraint.LONG_OR_DOUBLE);
    assertThat(startingState.getValue(1)).isNull();
    assertThat(startingState.getValue(2)).isNotNull();
    SymbolicValue longArg = startingState.getValue(3);
    assertThat(longArg).isNotNull();
    assertThat(startingState.getConstraint(longArg, BytecodeEGWalker.StackValueCategoryConstraint.class)).isEqualTo(BytecodeEGWalker.StackValueCategoryConstraint.LONG_OR_DOUBLE);
  }

  @Test
  public void max_step_exception_should_log_warning_and_generate_behavior() {
    BytecodeEGWalker bytecodeEGWalker = new BytecodeEGWalker(new BehaviorCache(squidClassLoader), semanticModel) {
      @Override
      int maxSteps() {
        return 2;
      }
    };
    MethodBehavior methodBehavior = getMethodBehavior(BytecodeTestClass.class, "fun(ZLjava/lang/Object;)Ljava/lang/Object;", bytecodeEGWalker);
    assertThat(logTester.logs(LoggerLevel.DEBUG))
      .contains("Dataflow analysis is incomplete for method org.sonar.java.bytecode.se.testdata.BytecodeTestClass#fun(ZLjava/lang/Object;)Ljava/lang/Object;" +
          " : Too many steps resolving org.sonar.java.bytecode.se.testdata.BytecodeTestClass#fun(ZLjava/lang/Object;)Ljava/lang/Object;");
    assertThat(methodBehavior.isComplete()).isFalse();
    assertThat(methodBehavior.isVisited()).isTrue();
  }

  @Test
  public void unchecked_exceptions_should_be_enqueued() {
    MethodBehavior mb = getMethodBehavior(ExceptionEnqueue.class, "test(Lorg/sonar/java/bytecode/se/testdata/ExceptionEnqueue;)Ljava/lang/Object;");
    List<Constraint> resultConstraint = mb.happyPathYields().map(y -> y.resultConstraint().get(ObjectConstraint.class)).collect(Collectors.toList());
    assertThat(resultConstraint).contains(ObjectConstraint.NOT_NULL, ObjectConstraint.NULL);
    List<String> exceptions = mb.exceptionalPathYields().map(y -> y.exceptionType(semanticModel).fullyQualifiedName()).collect(Collectors.toList());
    assertThat(exceptions).contains("org.sonar.java.bytecode.se.testdata.ExceptionEnqueue$ExceptionCatch",
        "org.sonar.java.bytecode.se.testdata.ExceptionEnqueue$ThrowableCatch",
        "org.sonar.java.bytecode.se.testdata.ExceptionEnqueue$ErrorCatch");
  }

  @Test
  public void test_enqueueing_of_catch_blocks() {
    MethodBehavior mb = getMethodBehavior(ExceptionEnqueue.class, "testCatchBlockEnqueue(Lorg/sonar/java/bytecode/se/testdata/ExceptionEnqueue;)Z");
    List<HappyPathYield> happyPathYields = mb.happyPathYields().collect(Collectors.toList());
    assertThat(happyPathYields).hasSize(1);
    assertThat(happyPathYields.get(0).resultConstraint()).isNull();
    List<ExceptionalYield> exceptionalYields = mb.exceptionalPathYields().collect(Collectors.toList());
    assertThat(exceptionalYields).hasSize(1);
    assertThat(exceptionalYields.get(0).exceptionType(semanticModel).is("java.lang.RuntimeException")).isTrue();
  }

  @Test
  public void test_enqueueing_of_catch_blocks2() {
    MethodBehavior mb = getMethodBehavior(ExceptionEnqueue.class, "testCatchBlockEnqueue2()Z");
    List<MethodYield> yields = mb.yields();
    assertThat(yields).hasSize(1);
    // result should have TRUE constraint, but wrong yield with FALSE constraint is also created
    // and two yields are reduced subsequently
    assertThat(mb.happyPathYields().findFirst().get().resultConstraint()).isNull();
    assertThat(mb.exceptionalPathYields().findFirst().isPresent()).isFalse();
  }

  @Test
  public void test_enqueueing_of_exit_block() {
    MethodBehavior mb = getMethodBehavior(ExceptionEnqueue.class, "enqueueExitBlock()Z");
    List<MethodYield> yields = mb.yields();
    assertThat(yields).hasSize(1);
    assertThat(mb.happyPathYields().findFirst().isPresent()).isFalse();
    ExceptionalYield exceptionalYield = mb.exceptionalPathYields().findFirst().get();
    Type exceptionType = exceptionalYield.exceptionType(semanticModel);
    assertThat(exceptionType.is("java.io.FileNotFoundException")).isTrue();
  }

  @Test
  public void test_enqueueing_of_exit_block2() {
    MethodBehavior mb = getMethodBehavior(ExceptionEnqueue.class, "enqueueExitBlock2(Lorg/sonar/java/bytecode/se/testdata/ExceptionEnqueue;)Z");
    List<HappyPathYield> happyPathYields = mb.happyPathYields().collect(Collectors.toList());
    assertThat(happyPathYields).hasSize(1);
    assertThat(happyPathYields.get(0).resultConstraint()).isNull();
    List<ExceptionalYield> exceptionalYields = mb.exceptionalPathYields().collect(Collectors.toList());
    assertThat(exceptionalYields).hasSize(1);
    assertThat(exceptionalYields.get(0).exceptionType(semanticModel).is("java.io.IOException")).isTrue();
  }

  @Test
  public void test_enqueueing_of_exit_block3() {
    MethodBehavior mb = getMethodBehavior(ExceptionEnqueue.class, "enqueueExitBlock3()Z");
    assertThat(mb.happyPathYields().findFirst().isPresent()).isFalse();
    List<ExceptionalYield> exceptionalYields = mb.exceptionalPathYields().collect(Collectors.toList());
    assertThat(exceptionalYields).hasSize(1);
    assertThat(exceptionalYields.get(0).exceptionType(semanticModel).is("java.io.FileNotFoundException")).isTrue();
  }

  @Test
  public void test_enqueueing_of_exit_block4() {
    MethodBehavior mb = getMethodBehavior(ExceptionEnqueue.class, "enqueueExitBlock4()Z");
    List<HappyPathYield> happyPathYields = mb.happyPathYields().collect(Collectors.toList());
    assertThat(happyPathYields.get(0).resultConstraint().hasConstraint(BooleanConstraint.TRUE)).isTrue();
    assertThat(mb.exceptionalPathYields().findFirst().isPresent()).isFalse();
  }

  @Test
  public void propagation_of_bytecode_analysis_exception() throws Exception {
    MethodBehavior methodBehavior = getMethodBehavior(MaxRelationBytecode.class, "isXMLLetter(C)Z");
    assertThat(methodBehavior.isComplete()).isFalse();
  }

  @Test
  public void test_zzz() {
    String cpString = "C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\slf4j\\slf4j-api\\1.7.21\\slf4j-api-1.7.21.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\slf4j\\jcl-over-slf4j\\1.7.21\\jcl-over-slf4j-1.7.21.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\slf4j\\log4j-over-slf4j\\1.7.21\\log4j-over-slf4j-1.7.21.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\slf4j\\jul-to-slf4j\\1.7.21\\jul-to-slf4j-1.7.21.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\ch\\qos\\logback\\logback-access\\1.1.7\\logback-access-1.1.7.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\ch\\qos\\logback\\logback-classic\\1.1.7\\logback-classic-1.1.7.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\ch\\qos\\logback\\logback-core\\1.1.7\\logback-core-1.1.7.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\tomcat\\embed\\tomcat-embed-core\\8.5.16\\tomcat-embed-core-8.5.16.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\google\\code\\gson\\gson\\2.3.1\\gson-2.3.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\h2database\\h2\\1.3.176\\h2-1.3.176.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-core\\6.5\\sonar-core-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\codehaus\\sonar\\sonar-classloader\\1.0\\sonar-classloader-1.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-db-dao\\6.5\\sonar-db-dao-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-db-core\\6.5\\sonar-db-core-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\commons\\commons-csv\\1.4\\commons-csv-1.4.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\mybatis\\mybatis\\3.4.4\\mybatis-3.4.4.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-db-migration\\6.5\\sonar-db-migration-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-scanner-protocol\\6.5\\sonar-scanner-protocol-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\net\\jpountz\\lz4\\lz4\\1.3.0\\lz4-1.3.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-markdown\\6.5\\sonar-markdown-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-process\\6.5\\sonar-process-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\update-center\\sonar-update-center-common\\1.18.0.487\\sonar-update-center-common-1.18.0.487.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\google\\guava\\guava\\18.0\\guava-18.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-plugin-api\\6.5\\sonar-plugin-api-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\codehaus\\woodstox\\woodstox-core-lgpl\\4.4.0\\woodstox-core-lgpl-4.4.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\codehaus\\woodstox\\stax2-api\\3.1.4\\stax2-api-3.1.4.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\codehaus\\staxmate\\staxmate\\2.0.1\\staxmate-2.0.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-ce-api\\6.5\\sonar-ce-api-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\commons-beanutils\\commons-beanutils\\1.8.3\\commons-beanutils-1.8.3.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\commons-dbutils\\commons-dbutils\\1.5\\commons-dbutils-1.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\commons\\commons-email\\1.3.2\\commons-email-1.3.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\javax\\mail\\mail\\1.4.5\\mail-1.4.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\javax\\activation\\activation\\1.1.1\\activation-1.1.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\commons-io\\commons-io\\2.4\\commons-io-2.4.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\commons-lang\\commons-lang\\2.6\\commons-lang-2.6.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\picocontainer\\picocontainer\\2.15\\picocontainer-2.15.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\commons-codec\\commons-codec\\1.8\\commons-codec-1.8.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\commons-dbcp\\commons-dbcp\\1.4\\commons-dbcp-1.4.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\commons-pool\\commons-pool\\1.5.4\\commons-pool-1.5.4.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\elasticsearch\\elasticsearch\\2.4.4\\elasticsearch-2.4.4.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-core\\5.5.2\\lucene-core-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-backward-codecs\\5.5.2\\lucene-backward-codecs-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-analyzers-common\\5.5.2\\lucene-analyzers-common-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-queries\\5.5.2\\lucene-queries-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-memory\\5.5.2\\lucene-memory-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-highlighter\\5.5.2\\lucene-highlighter-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-queryparser\\5.5.2\\lucene-queryparser-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-sandbox\\5.5.2\\lucene-sandbox-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-suggest\\5.5.2\\lucene-suggest-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-misc\\5.5.2\\lucene-misc-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-join\\5.5.2\\lucene-join-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-grouping\\5.5.2\\lucene-grouping-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-spatial\\5.5.2\\lucene-spatial-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\apache\\lucene\\lucene-spatial3d\\5.5.2\\lucene-spatial3d-5.5.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\spatial4j\\spatial4j\\0.5\\spatial4j-0.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\elasticsearch\\securesm\\1.0\\securesm-1.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\carrotsearch\\hppc\\0.7.1\\hppc-0.7.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\joda-time\\joda-time\\2.9.5\\joda-time-2.9.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\fasterxml\\jackson\\core\\jackson-core\\2.6.6\\jackson-core-2.6.6.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\fasterxml\\jackson\\dataformat\\jackson-dataformat-smile\\2.8.1\\jackson-dataformat-smile-2.8.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\fasterxml\\jackson\\dataformat\\jackson-dataformat-yaml\\2.8.1\\jackson-dataformat-yaml-2.8.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\fasterxml\\jackson\\dataformat\\jackson-dataformat-cbor\\2.8.1\\jackson-dataformat-cbor-2.8.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\yaml\\snakeyaml\\1.15\\snakeyaml-1.15.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\io\\netty\\netty\\3.10.6.Final\\netty-3.10.6.Final.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\ning\\compress-lzf\\1.0.2\\compress-lzf-1.0.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\tdunning\\t-digest\\3.0\\t-digest-3.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\hdrhistogram\\HdrHistogram\\2.1.6\\HdrHistogram-2.1.6.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\commons-cli\\commons-cli\\1.3.1\\commons-cli-1.3.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\twitter\\jsr166e\\1.1.0\\jsr166e-1.1.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\elasticsearch\\elasticsearch\\2.4.4\\elasticsearch-2.4.4-tests.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\net\\java\\dev\\jna\\jna\\4.1.0\\jna-4.1.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\google\\protobuf\\protobuf-java\\3.0.0-beta-2\\protobuf-java-3.0.0-beta-2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-ws\\6.5\\sonar-ws-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\squareup\\okhttp3\\okhttp\\3.7.0\\okhttp-3.7.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\squareup\\okio\\okio\\1.12.0\\okio-1.12.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\google\\code\\findbugs\\jsr305\\3.0.2\\jsr305-3.0.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-plugin-bridge\\6.5\\sonar-plugin-bridge-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\io\\jsonwebtoken\\jjwt\\0.6.0\\jjwt-0.6.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\fasterxml\\jackson\\core\\jackson-databind\\2.6.6\\jackson-databind-2.6.6.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\fasterxml\\jackson\\core\\jackson-annotations\\2.6.6\\jackson-annotations-2.6.6.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\junit\\junit\\4.12\\junit-4.12.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\hamcrest\\hamcrest-core\\1.3\\hamcrest-core-1.3.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\assertj\\assertj-core\\3.4.1\\assertj-core-3.4.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\assertj\\assertj-guava\\3.0.0\\assertj-guava-3.0.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\mockito\\mockito-core\\1.10.19\\mockito-core-1.10.19.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\objenesis\\objenesis\\2.1\\objenesis-2.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\hamcrest\\hamcrest-all\\1.3\\hamcrest-all-1.3.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-db-testing\\6.5\\sonar-db-testing-6.5.pom;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-testing-harness\\6.5\\sonar-testing-harness-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\googlecode\\json-simple\\json-simple\\1.1.1\\json-simple-1.1.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-db-core\\6.5\\sonar-db-core-6.5-tests.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-db-dao\\6.5\\sonar-db-dao-6.5-tests.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\dbunit\\dbunit\\2.4.5\\dbunit-2.4.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\commons-collections\\commons-collections\\3.2.1\\commons-collections-3.2.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\github\\tlrx\\elasticsearch-test\\1.2.1\\elasticsearch-test-1.2.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\tngtech\\java\\junit-dataprovider\\1.9.2\\junit-dataprovider-1.9.2.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\github\\kevinsawicki\\http-request\\5.4.1\\http-request-5.4.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\sonarsource\\sonarqube\\sonar-search\\6.5\\sonar-search-6.5.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\reflections\\reflections\\0.9.9\\reflections-0.9.9.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\javassist\\javassist\\3.18.2-GA\\javassist-3.18.2-GA.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\google\\code\\findbugs\\annotations\\2.0.1\\annotations-2.0.1.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\subethamail\\subethasmtp\\3.1.7\\subethasmtp-3.1.7.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\com\\squareup\\okhttp3\\mockwebserver\\3.7.0\\mockwebserver-3.7.0.jar;C:\\Users\\Tibor Blenessy\\.m2\\repository\\org\\bouncycastle\\bcprov-jdk15on\\1.50\\bcprov-jdk15on-1.50.jar";
    SquidClassLoader cl = new SquidClassLoader(Arrays.stream(cpString.split(";")).map(File::new).collect(Collectors.toList()));
    String signature = "org.sonar.server.computation.task.projectanalysis.qualitymodel.RatingSettings#getDefaultDevelopmentCost()J";
    String file = "C:\\projects\\sonar-java\\its\\sources\\sonarqube-6.5\\server\\sonar-server\\src\\main\\java\\org\\sonar\\server\\computation\\task\\projectanalysis\\qualitymodel\\RatingSettings.java";
    SymbolicExecutionVisitor sev = SETestUtils.createSymbolicExecutionVisitor(file, cl, new InvariantReturnCheck());
    MethodBehavior mb = sev.behaviorCache.behaviors.get(signature);
    System.out.println(mb);
  }

  @Test
  public void test_zzz2() {
    MethodBehavior mb = getBytecodeEGWalker(squidClassLoader).getMethodBehavior("java.lang.Long#parseLong(Ljava/lang/String;)J", squidClassLoader);
    System.out.println(mb);
  }


  private static String desc(Class<?> owner, String method, Class<?> ret, Class<?>... args) {
    StringBuilder sb = new StringBuilder();
    sb.append(owner.getCanonicalName())
        .append("#")
        .append(method)
        .append("(");
    Arrays.stream(args).map(BytecodeEGWalkerTest::desc).forEach(sb::append);
    sb.append(")").append(desc(ret));
    return sb.toString();
  }

  private static String desc(Class<?> owner) {
    return org.objectweb.asm.Type.getType(owner).getDescriptor();
  }

  private static MethodBehavior getMethodBehavior(String signature) {
    return getMethodBehavior(BytecodeTestClass.class, signature);
  }

  private static MethodBehavior getMethodBehavior(Class<?> clazz, String signature) {
    return getMethodBehavior(clazz, signature, getBytecodeEGWalker(squidClassLoader));
  }

  private static MethodBehavior getMethodBehavior(Class<?> clazz, String signature, BytecodeEGWalker walker) {
    return walker.getMethodBehavior(clazz.getCanonicalName() + "#" + signature, squidClassLoader);
  }

  private static BytecodeEGWalker getBytecodeEGWalker(SquidClassLoader squidClassLoader) {
    BehaviorCache behaviorCache = new BehaviorCache(squidClassLoader);
    behaviorCache.setFileContext(null, semanticModel);
    return new BytecodeEGWalker(behaviorCache, semanticModel);
  }

}
