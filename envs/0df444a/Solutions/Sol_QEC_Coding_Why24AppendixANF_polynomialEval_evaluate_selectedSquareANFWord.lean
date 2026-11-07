-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.polynomialEval_evaluate_selectedSquareANFWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:57:32.739358+00:00
-- url     : https://prove2.me/submissions/66dbb01c-0b51-4d25-b32e-dbcaa6522659

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_evaluate_linearANFWord
import Theorems.Thm_QEC_Coding_Why24AppendixANF_selectedCoordinates_symm_eq_sum
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
private theorem bit_smul_square (bit : ZMod 2) (value : F1024) :
    (bit • value) ^ 2 = bit • value ^ 2 := by
  simp only [Algebra.smul_def, mul_pow, ← map_pow]
  rw [ZMod.pow_card]
private theorem sum_bit_smul_square (word : Word) (values : Fin 10 → F1024) :
    (∑ selected : Fin 10, word selected • values selected) ^ 2 =
      ∑ selected : Fin 10, word selected • values selected ^ 2 := by
  calc
    (∑ selected : Fin 10, word selected • values selected) ^ 2 =
        ∑ selected : Fin 10, (word selected • values selected) ^ 2 := by
          simpa using
            (sum_pow_char (R := F1024) (p := 2)
              (Finset.univ : Finset (Fin 10))
              (fun selected => word selected • values selected))
    _ = ∑ selected : Fin 10, word selected • values selected ^ 2 := by
      apply Finset.sum_congr rfl
      intro selected _
      exact bit_smul_square (word selected) (values selected)
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
    polynomialEval (fun power => evaluate word (selectedSquareANFWord power)) =
      (f1024SelectedCoordinates.symm word) ^ 2 := by
  rw [selectedSquareANFWord, polynomialEval_evaluate_linearANFWord]
  simp_rw [polynomialEval_selectedBasisSquareWord]
  rw [← sum_bit_smul_square, ← selectedCoordinates_symm_eq_sum]
end QEC.Coding.Why24AppendixANF
