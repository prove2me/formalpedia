-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.traceTensor_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:58:07.877149+00:00
-- url     : https://prove2.me/submissions/fd530b19-f317-43a9-a55f-7d0c6f306413

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Theorems.Thm_QEC_Coding_Why24AppendixANF_trace_polynomialEval_eq_seven
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisFourthWord
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisSquareWord
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisWord
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_wordMul
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.Why24BooleanANF.evaluate_generator
attribute [local simp] QEC.Coding.Why24BooleanANF.generator_mul_self
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (first second third : Fin 10) :
    traceTensor first second third =
      Algebra.trace (ZMod 2) F1024
        (f1024SelectedSelfDualBasis first *
          f1024SelectedSelfDualBasis second ^ 2 *
          f1024SelectedSelfDualBasis third ^ 4) := by
  have heval :
      polynomialEval
          (wordMul
            (wordMul (selectedBasisWord first) (selectedBasisSquareWord second))
            (selectedBasisFourthWord third)) =
        f1024SelectedSelfDualBasis first *
          f1024SelectedSelfDualBasis second ^ 2 *
          f1024SelectedSelfDualBasis third ^ 4 := by
    rw [polynomialEval_wordMul, polynomialEval_wordMul,
      polynomialEval_selectedBasisWord,
      polynomialEval_selectedBasisSquareWord,
      polynomialEval_selectedBasisFourthWord]
  have htrace := congrArg (Algebra.trace (ZMod 2) F1024) heval
  rw [trace_polynomialEval_eq_seven] at htrace
  simpa only [traceTensor] using htrace
end QEC.Coding.Why24AppendixANF
