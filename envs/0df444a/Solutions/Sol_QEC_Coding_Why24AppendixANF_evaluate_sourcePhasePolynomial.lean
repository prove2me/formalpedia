-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.evaluate_sourcePhasePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:00:36.403606+00:00
-- url     : https://prove2.me/submissions/f5c089e0-ca1c-4f02-ab4f-bf80910662ae

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_evaluate_linearANFWord
import Theorems.Thm_QEC_Coding_Why24AppendixANF_selectedCoordinates_symm_eq_sum
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_evaluate_selectedSquareANFWord
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_evaluate_selectedFourthANFWord
import Theorems.Thm_QEC_Coding_Why24AppendixANF_traceTensor_eq_trace
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisFourthWord
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisSquareWord
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


section
noncomputable section
namespace QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
private theorem trace_selected_triple_sums (word : Word) :
    Algebra.trace (ZMod 2) F1024
        ((∑ first : Fin 10,
            word first • f1024SelectedSelfDualBasis first) *
          (∑ second : Fin 10,
            word second • f1024SelectedSelfDualBasis second ^ 2) *
          (∑ third : Fin 10,
            word third • f1024SelectedSelfDualBasis third ^ 4)) =
      ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
        (word first * word second * word third) *
          Algebra.trace (ZMod 2) F1024
            (f1024SelectedSelfDualBasis first *
              f1024SelectedSelfDualBasis second ^ 2 *
              f1024SelectedSelfDualBasis third ^ 4) := by
  rw [Fintype.sum_mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  have hterm :
      (word first • f1024SelectedSelfDualBasis first) *
          (word second • f1024SelectedSelfDualBasis second ^ 2) *
          (word third • f1024SelectedSelfDualBasis third ^ 4) =
        (word first * word second * word third) •
          (f1024SelectedSelfDualBasis first *
            f1024SelectedSelfDualBasis second ^ 2 *
            f1024SelectedSelfDualBasis third ^ 4) := by
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [hterm, (Algebra.trace (ZMod 2) F1024).map_smul]
  simp only [smul_eq_mul]
end QEC.Coding.Why24AppendixANF
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (word : Word) :
    evaluate word sourcePhasePolynomial =
      Algebra.trace (ZMod 2) F1024
        ((f1024SelectedCoordinates.symm word) ^ 7) := by
  have hevaluate :
      evaluate word sourcePhasePolynomial =
        ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
          (word first * word second * word third) *
            Algebra.trace (ZMod 2) F1024
              (f1024SelectedSelfDualBasis first *
                f1024SelectedSelfDualBasis second ^ 2 *
                f1024SelectedSelfDualBasis third ^ 4) := by
    rw [sourcePhasePolynomial, map_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro second _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro third _
    simp only [map_smul, map_mul, evaluate_generator, smul_eq_mul]
    rw [traceTensor_eq_trace]
    ring
  rw [hevaluate, ← trace_selected_triple_sums,
    ← selectedCoordinates_symm_eq_sum]
  have hsquare := polynomialEval_evaluate_selectedSquareANFWord word
  have hfourth := polynomialEval_evaluate_selectedFourthANFWord word
  rw [selectedSquareANFWord, polynomialEval_evaluate_linearANFWord] at hsquare
  rw [selectedFourthANFWord, polynomialEval_evaluate_linearANFWord] at hfourth
  simp_rw [polynomialEval_selectedBasisSquareWord] at hsquare
  simp_rw [polynomialEval_selectedBasisFourthWord] at hfourth
  rw [hsquare, hfourth]
  congr 1
  ring
end QEC.Coding.Why24AppendixANF
