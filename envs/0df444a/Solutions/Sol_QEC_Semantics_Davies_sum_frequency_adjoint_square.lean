-- Prove2me | solution 1 for QEC.Semantics.Davies.sum_frequency_adjoint_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:07:59.183521+00:00
-- url     : https://prove2.me/submissions/8b747438-8d8f-4ee0-9484-87825ee6390f

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Theorems.Thm_QEC_Semantics_Davies_entry_adjoint
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_ext
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
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
theorem _root_.solution (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : Operator V) :
    (∑ ω : Frequency e, LinearMap.adjoint (frequencyComponent b e A ω.val) *
      frequencyComponent b e A ω.val) =
      frequencyComponent b e (LinearMap.adjoint A * A) 0 := by
  apply entry_ext b
  intro i j
  simp only [entry_sum, entry_mul, entry_adjoint, entry_frequencyComponent]
  rw [Finset.sum_comm]
  have hs : (if e j-e i = 0 then ∑ k, star (entry b A k i) * entry b A k j else 0) =
      ∑ k, if e j-e i = 0 then star (entry b A k i) * entry b A k j else 0 := by
    split_ifs <;> simp
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  let w : Frequency e := ⟨e i-e k, (mem_frequencies _ _).mpr ⟨k,i,rfl⟩⟩
  rw [Finset.sum_eq_single w]
  · dsimp [w]
    by_cases he : e i = e j
    · simp [he]
    · have hd : e j-e k ≠ e i-e k := by intro h; apply he; linarith
      simp [he, Ne.symm he, hd, sub_eq_zero]
  · intro z _ hzw
    have hz : e i-e k ≠ z.val := by
      intro h
      exact hzw (Subtype.ext h.symm)
    simp [hz]
  · simp
end QEC.Semantics.Davies
