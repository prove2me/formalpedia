-- Prove2me | solution 1 for QEC.Semantics.Davies.energyProjector_apply_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:08:02.039851+00:00
-- url     : https://prove2.me/submissions/6e71684d-7f39-484c-b76e-4a0a01c042e7

import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero
import Theorems.Thm_QEC_Semantics_Davies_diagonal_apply_repr
import Theorems.Thm_QEC_Semantics_Davies_energyProjector_apply_repr
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


attribute [local simp] QEC.Semantics.Davies.entry_frequencyComponent
attribute [local simp] QEC.Semantics.Davies.entry_diagonal_mul
attribute [local simp] QEC.Semantics.Davies.entry_mul_diagonal
attribute [local simp] QEC.Semantics.Davies.frequencyComponent_zero

set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (x : V) (lam E : ℝ) (hx : diagonal b e x = (lam : ℂ) • x) :
    energyProjector b e E x = if lam = E then x else 0 := by
  apply b.repr.injective
  ext i
  have h := congrArg (fun y => b.repr y i) hx
  rw [diagonal_apply_repr] at h
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul] at h
  have hz (he : e i ≠ lam) : b.repr x i = 0 := by
    have hne : (e i : ℂ) - (lam : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast he)
    exact (mul_eq_zero.mp (show ((e i : ℂ)-(lam : ℂ))*b.repr x i = 0 by
      linear_combination h)).resolve_left hne
  rw [energyProjector_apply_repr]
  by_cases hlam : lam = E
  · subst E
    by_cases he : e i = lam
    · simp [he]
    · simp [he, hz he]
  · by_cases he : e i = E
    · have hne : e i ≠ lam := by intro h; exact hlam (h.symm.trans he)
      simp [hlam, he, hz hne]
    · simp [hlam, he]
end QEC.Semantics.Davies
