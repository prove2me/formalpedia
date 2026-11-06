-- Prove2me | solution 1 for QEC.Locality.refill_comp_erasure_matrix_element
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:55:02.303493+00:00
-- url     : https://prove2.me/submissions/f454c57f-1476-4e6b-89ef-c23b94d4a19a

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_erasureChannel_apply_eq_leftCompression
import Theorems.Thm_QEC_Locality_inner_ket_eq_ite
import Theorems.Thm_QEC_Locality_sum_double_delta
import Theorems.Thm_QEC_Locality_scaled_refill_contribution_matrix_element
import Theorems.Thm_QEC_Locality_leftCompression_matrix_element
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
      ((QuantumChannel.comp (refillFactorized S) S.erasureChannel).toLinearMap A
        (ket a ⊗ₜ[Complex] k)) =
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
  change inner Complex (ket b ⊗ₜ[Complex] l)
    ((refillFactorized S).toLinearMap (S.erasureChannel A)
      (ket a ⊗ₜ[Complex] k)) = _
  rw [erasureChannel_apply_eq_leftCompression]
  unfold refillFactorized
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  rw [inner_sum, Fintype.sum_prod_type]
  simp only [refillFamilyFactorized, FiniteKrausFamily.scale_operator,
    refillUnnormalizedFamilyFactorized]
  simp_rw [scaled_refill_contribution_matrix_element S (localPauliAmplitude S)]
  by_cases hba : b = a
  · subst b
    rw [if_pos rfl]
    simp only [inner_ket_eq_ite]
    simp_rw [Finset.sum_const, Finset.card_univ]
    simp_rw [← Nat.cast_smul_eq_nsmul Complex]
    simp only [smul_eq_mul]
    change (∑ x : Qubit.Bitstring S.SelectedCoordinates,
      d * (((star (localPauliAmplitude S) * localPauliAmplitude S *
          (if a = x then 1 else 0)) * (if x = a then 1 else 0)) *
        inner Complex l (leftCompression S A k))) = _
    have hcollapse :
        (∑ x : Qubit.Bitstring S.SelectedCoordinates,
          d * (((star (localPauliAmplitude S) * localPauliAmplitude S *
              (if a = x then 1 else 0)) * (if x = a then 1 else 0)) *
            inner Complex l (leftCompression S A k))) =
          (d * (star (localPauliAmplitude S) * localPauliAmplitude S)) *
            inner Complex l (leftCompression S A k) := by
      calc
        (∑ x : Qubit.Bitstring S.SelectedCoordinates,
          d * (((star (localPauliAmplitude S) * localPauliAmplitude S *
              (if a = x then 1 else 0)) * (if x = a then 1 else 0)) *
            inner Complex l (leftCompression S A k))) =
          ∑ x : Qubit.Bitstring S.SelectedCoordinates,
            (d * (star (localPauliAmplitude S) * localPauliAmplitude S)) *
              (if a = x then 1 else 0) * (if x = a then 1 else 0) *
              inner Complex l (leftCompression S A k) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
        _ = _ := sum_double_delta a
          (d * (star (localPauliAmplitude S) * localPauliAmplitude S))
          (inner Complex l (leftCompression S A k))
    rw [hcollapse, leftCompression_matrix_element]
    rw [hstar_amp, hamp]
    field_simp
  · rw [if_neg hba]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro z _
    have hprod : inner Complex (ket b) (ket x) * inner Complex (ket x) (ket a) = 0 := by
      by_cases hbx : b = x
      · subst x
        rw [inner_ket_self, inner_ket_eq_ite, if_neg hba]
        simp
      · rw [inner_ket_eq_ite, if_neg hbx]
        simp
    calc
      star (localPauliAmplitude S) * localPauliAmplitude S *
          inner Complex (ket b) (ket x) * inner Complex (ket x) (ket a) *
          inner Complex l (leftCompression S A k) =
        (star (localPauliAmplitude S) * localPauliAmplitude S) *
          (inner Complex (ket b) (ket x) * inner Complex (ket x) (ket a)) *
          inner Complex l (leftCompression S A k) := by ring
      _ = 0 := by rw [hprod]; simp
end QEC.Locality
