-- Prove2me | solution 1 for QEC.Semantics.Davies.entry_eq_zero_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:12:40.843917+00:00
-- url     : https://prove2.me/submissions/d995c236-1113-4e89-b197-57dd6f0cdcce

import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
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
    (A : Operator V) (hA : Commute (diagonal b e) A) (i j : ι)
    (hne : e i ≠ e j) : entry b A i j = 0 := by
  have h := congrArg (fun T => entry b T i j) hA.eq
  simp only [entry_diagonal_mul, entry_mul_diagonal] at h
  have hc : (e i : ℂ) - (e j : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  apply (mul_eq_zero.mp (show ((e i : ℂ) - (e j : ℂ)) * entry b A i j = 0 by linear_combination h)).resolve_left hc
end QEC.Semantics.Davies
