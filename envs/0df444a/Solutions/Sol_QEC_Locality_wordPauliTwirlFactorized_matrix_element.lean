-- Prove2me | solution 1 for QEC.Locality.wordPauliTwirlFactorized_matrix_element
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:56:11.330582+00:00
-- url     : https://prove2.me/submissions/2aca72f7-cb71-4fde-a5cc-8b5b7570b76e

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_sum_binaryPhase_wordPairing
import Theorems.Thm_QEC_Locality_card_word_eq_card_bitstring
import Theorems.Thm_QEC_Locality_word_add_self_zero
import Theorems.Thm_QEC_Locality_bitstringWord_add_eq_zero_iff
import Theorems.Thm_QEC_Locality_scaled_wordPauli_contribution_matrix_element
import Theorems.Thm_QEC_Locality_flipWordEquiv_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
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
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
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
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (wordPauliTwirlFactorized S A (ket a ⊗ₜ[Complex] k)) =
      if b = a then
        localPauliAmplitude S *
          ∑ h : Qubit.Bitstring S.SelectedCoordinates,
            inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k))
      else 0 := by
  let d : Complex := Fintype.card (Qubit.Bitstring S.SelectedCoordinates)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast Fintype.card_ne_zero
  have hamp : localPauliAmplitude S = d⁻¹ := by rfl
  have hstar_amp : star (localPauliAmplitude S) = localPauliAmplitude S := by
    unfold localPauliAmplitude
    simp
  have hsum :
      inner Complex (ket b ⊗ₜ[Complex] l)
        (wordPauliTwirlFactorized S A (ket a ⊗ₜ[Complex] k)) =
      ∑ x : Coding.Word (ZMod 2) S.SelectedCoordinates,
        ∑ z : Coding.Word (ZMod 2) S.SelectedCoordinates,
          (star (localPauliAmplitude S) * localPauliAmplitude S) *
            PauliSymplectic.binaryPhaseScalar
              (Coding.wordPairing (F := ZMod 2) (ι := S.SelectedCoordinates) z
                ((PauliSymplectic.bitstringWordEquiv _ b) +
                  PauliSymplectic.bitstringWordEquiv _ a)) *
            inner Complex
              (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) b) ⊗ₜ[Complex] l)
              (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] k)) := by
    change inner Complex (ket b ⊗ₜ[Complex] l)
      ((wordPauliTwirlFactorized S).toLinearMap A (ket a ⊗ₜ[Complex] k)) = _
    unfold wordPauliTwirlFactorized
    rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
    simp only [LinearMap.coe_sum, Finset.sum_apply]
    rw [inner_sum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    exact scaled_wordPauli_contribution_matrix_element S (localPauliAmplitude S) (x, z)
      A a b k l
  rw [hsum]
  by_cases hba : b = a
  · subst b
    rw [if_pos rfl]
    simp only [word_add_self_zero, map_zero,
      PauliSymplectic.binaryPhaseScalar_zero, mul_one]
    simp_rw [Finset.sum_const, Finset.card_univ]
    have hcard : (Fintype.card (Coding.Word (ZMod 2) S.SelectedCoordinates) : Complex) = d := by
      rw [card_word_eq_card_bitstring]
    simp_rw [← Nat.cast_smul_eq_nsmul Complex]
    rw [hcard]
    rw [← Finset.smul_sum]
    change d * (∑ x : Coding.Word (ZMod 2) S.SelectedCoordinates,
      star (localPauliAmplitude S) * localPauliAmplitude S *
        inner Complex
          (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] l)
          (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] k))) = _
    rw [← Finset.mul_sum]
    have hflip :
        (∑ x : Coding.Word (ZMod 2) S.SelectedCoordinates,
          inner Complex
            (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] l)
            (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport x) a) ⊗ₜ[Complex] k))) =
          ∑ h : Qubit.Bitstring S.SelectedCoordinates,
            inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k)) := by
      apply Fintype.sum_equiv (flipWordEquiv a)
      intro x
      exact congrArg (fun h : Qubit.Bitstring S.SelectedCoordinates =>
        inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k)))
        (flipWordEquiv_apply a x).symm
    rw [hflip]
    rw [hstar_amp, hamp]
    field_simp
  · rw [if_neg hba]
    have hzero : PauliSymplectic.bitstringWordEquiv S.SelectedCoordinates b +
        PauliSymplectic.bitstringWordEquiv S.SelectedCoordinates a ≠ 0 := by
      intro hz
      exact hba ((bitstringWord_add_eq_zero_iff a b).1 hz)
    apply Finset.sum_eq_zero
    intro x _
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_binaryPhase_wordPairing, if_neg hzero]
    simp
end QEC.Locality
