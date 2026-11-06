-- Prove2me | solution 2 for QEC.Semantics.Davies.actualFrequency_add_commuting_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:05:05.575866+00:00
-- url     : https://prove2.me/submissions/59b6ac57-f50e-4536-b4c4-764ac064579f

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_sum
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_of_not_mem
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_of_eigenoperator
import Theorems.Thm_QEC_Semantics_Davies_actualFrequency_energyDifference
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_mul_left
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_mul_right
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero
import Theorems.Thm_QEC_Semantics_Davies_hamiltonian_diagonal
import Theorems.Thm_QEC_Semantics_Davies_sum_frequencyComponent
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_one
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_zero
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.Davies.entry_diagonal_mul
attribute [local simp] QEC.Semantics.Davies.entry_frequencyComponent
attribute [local simp] QEC.Semantics.Davies.entry_mul_diagonal
attribute [local simp] QEC.Semantics.Davies.frequencyComponent_zero
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocalToRegister_one
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocalToRegister_zero
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (L R A : Operator V)
    (hL : L.IsSymmetric) (hH : (L+R).IsSymmetric)
    (hLR : Commute L R) (hRA : Commute R A) (ω : ℝ) :
    actualFrequency (L+R) hH A ω = actualFrequency L hL A ω := by
  let b := hamiltonianBasis L hL
  let e := hamiltonianEnergies L hL
  have hR : Commute (diagonal b e) R := by simpa [b,e,hamiltonian_diagonal] using hLR
  have hc : ∀ freq, Commute R (frequencyComponent b e A freq) := by
    intro freq
    have h := congrArg (fun B => frequencyComponent b e B freq) hRA.eq
    rw [frequencyComponent_mul_left b e R A hR,
      frequencyComponent_mul_right b e A R hR] at h
    exact h
  have heig : ∀ freq, energyDifference (L+R) (frequencyComponent b e A freq) =
      (freq : ℂ) • frequencyComponent b e A freq := by
    intro freq
    have h := actualFrequency_energyDifference L hL A freq
    change energyDifference L (frequencyComponent b e A freq) = _ at h
    simp only [energyDifference, mul_add, add_mul] at h ⊢
    rw [(hc freq).eq]
    convert h using 1 <;> abel
  have hsum := sum_frequencyComponent b e A
  unfold actualFrequency
  conv_lhs => rw [← hsum]
  rw [frequencyComponent_sum]
  have hselect : ∀ freq,
      frequencyComponent (hamiltonianBasis (L+R) hH) (hamiltonianEnergies (L+R) hH)
        (frequencyComponent b e A freq) ω =
        if freq=ω then frequencyComponent b e A freq else 0 := by
    intro freq
    apply frequencyComponent_of_eigenoperator
    simpa only [hamiltonian_diagonal] using heig freq
  simp_rw [hselect]
  by_cases hw : ω ∈ frequencies e
  · let w : Frequency e := ⟨ω,hw⟩
    rw [Finset.sum_eq_single w]
    · simp [w,b,e]
    · intro k _ hk
      have hn : k.val ≠ ω := fun h => hk (Subtype.ext h)
      simp [hn]
    · simp
  · rw [frequencyComponent_of_not_mem b e A ω hw]
    apply Finset.sum_eq_zero
    intro k _
    have hn : k.val ≠ ω := fun h => hw (h ▸ k.property)
    simp [hn]
end QEC.Semantics.Davies
