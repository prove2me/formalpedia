-- Prove2me | solution 1 for QEC.Semantics.Davies.frequencyFilter_eq_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:15:00.896134+00:00
-- url     : https://prove2.me/submissions/7b6537b8-9d36-45d1-9c88-ac0c1473764c

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyFilter
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_ext
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero
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
theorem _root_.solution (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (ω : ℝ) (hω : ω ∈ frequencies e) (A : Operator V) :
    frequencyFilter (diagonal b e) ω ((frequencies e).erase ω).toList A =
      frequencyComponent b e A ω := by
  apply entry_ext b
  intro i j
  rw [entry_frequencyFilter, entry_frequencyComponent]
  by_cases hg : e j-e i = ω
  · rw [if_pos hg]
    have hp : (((frequencies e).erase ω).toList.map
        (fun ν => (((ω-ν : ℝ) : ℂ)⁻¹) * ((e j-e i-ν : ℝ) : ℂ))).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      obtain ⟨ν,hν,rfl⟩ := List.mem_map.mp hx
      have hn : ν ≠ ω := (Finset.mem_erase.mp (Finset.mem_toList.mp hν)).1
      rw [hg]
      exact inv_mul_cancel₀ (by exact_mod_cast (sub_ne_zero.mpr (Ne.symm hn)))
    rw [hp, one_mul]
  · rw [if_neg hg]
    have hm : e j-e i ∈ (frequencies e).erase ω :=
      Finset.mem_erase.mpr ⟨hg,(mem_frequencies _ _).2 ⟨i,j,rfl⟩⟩
    have hz : (0 : ℂ) ∈ (((frequencies e).erase ω).toList.map
        (fun ν => (((ω-ν : ℝ) : ℂ)⁻¹) * ((e j-e i-ν : ℝ) : ℂ))) := by
      apply List.mem_map.mpr
      exact ⟨e j-e i, Finset.mem_toList.mpr hm, by simp⟩
    rw [List.prod_eq_zero hz, zero_mul]
end QEC.Semantics.Davies
