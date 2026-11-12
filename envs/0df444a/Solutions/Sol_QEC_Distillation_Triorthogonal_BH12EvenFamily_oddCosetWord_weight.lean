-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.oddCosetWord_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:05:34.359207+00:00
-- url     : https://prove2.me/submissions/a11c805e-0ce9-4c33-8317-f3aefb074f9c

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.bitstringWordEquiv_reducedLogicalBits
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.physicalCliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
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
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
private theorem combineSix_self_sum (i : Fin 8) :
    (∑ j, (combineSix (coefficientBits i) j *
      combineSix (coefficientBits i) j).val) =
      ![0, 4, 4, 4, 0, 4, 4, 4] i := by
  fin_cases i <;> decide +kernel
private theorem sum_ite_fin_eq {q : Nat} (a : Fin q) (special regular : Nat) :
    (∑ j : Fin q, if j = a then special else regular) =
      special + (q - 1) * regular := by
  classical
  have hEq : (Finset.univ.filter fun j : Fin q => j = a) = {a} := by
    ext j
    simp
  have hNe : (Finset.univ.filter fun j : Fin q => ¬ j = a) = Finset.univ.erase a := by
    ext j
    simp [and_comm]
  rw [Finset.sum_ite]
  rw [hEq, hNe]
  simp
private theorem oddCoset_four_self_sum (i : Fin 8) :
    (∑ j : Fin 4,
        (combineFour (coefficientBits i) j *
          combineFour (coefficientBits i) j).val) +
      (∑ j : Fin 4,
        ((combineFour (coefficientBits i) j + 1) *
          (combineFour (coefficientBits i) j + 1)).val) = 4 := by
  fin_cases i <;> decide +kernel
private theorem oddCoset_special_six_self_sum (i : Fin 8) (b : Fin 2) :
    (∑ j : Fin 6,
      ((combineSix (coefficientBits i) j + oddBlock b j) *
        (combineSix (coefficientBits i) j + oddBlock b j)).val) = 3 := by
  fin_cases i <;> fin_cases b <;> decide +kernel
private theorem oddCoset_six_block_self_sum {q : Nat}
    (a : OddRow q) (i : Fin 8) (u : Fin q) :
    (∑ j : Fin 6,
      (oddCosetWord a i (Sum.inr (Sum.inr (u, j))) *
        oddCosetWord a i (Sum.inr (Sum.inr (u, j)))).val) =
      if u = a.1 then 3 else ![0, 4, 4, 4, 0, 4, 4, 4] i := by
  by_cases hua : u = a.1
  · simp [hua, oddCoset_special_six_self_sum]
  · simp [hua, combineSix_self_sum]
end QEC.Distillation.Triorthogonal.BH12EvenFamily
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution {q : Nat} (a : OddRow q) (i : Fin 8) :
    HammingWeight (oddCosetWord a i) =
      ![7, 3 + 4 * q, 3 + 4 * q, 3 + 4 * q, 7,
        3 + 4 * q, 3 + 4 * q, 3 + 4 * q] i := by
  rw [← BinaryRowFamily.pairOverlap_self_eq_hammingWeight]
  simp only [BinaryRowFamily.pairOverlap, Fintype.sum_sum_type,
    Fintype.sum_prod_type, oddCosetWord_first_apply,
    oddCosetWord_second_apply]
  rw [← Nat.add_assoc, oddCoset_four_self_sum]
  simp_rw [oddCoset_six_block_self_sum]
  rw [sum_ite_fin_eq a.1 3 (![0, 4, 4, 4, 0, 4, 4, 4] i)]
  have hq : 0 < q := Nat.zero_lt_of_lt a.1.isLt
  fin_cases i <;> simp <;> omega
end QEC.Distillation.Triorthogonal.BH12EvenFamily
