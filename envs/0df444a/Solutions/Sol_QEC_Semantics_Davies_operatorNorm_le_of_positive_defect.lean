-- Prove2me | solution 1 for QEC.Semantics.Davies.operatorNorm_le_of_positive_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:08:44.939965+00:00
-- url     : https://prove2.me/submissions/acda5412-0ea8-4de5-9af0-a09d1399364a

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
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
open scoped BigOperators ComplexOrder
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (A : Operator V) (c : ℝ) (hc : 0 ≤ c)
    (hA : A.IsPositive) (hdef : ((c : ℂ) • (1 : Operator V) - A).IsPositive) :
    operatorNorm A ≤ c := by
  let T := LinearMap.toContinuousLinearMap A
  have hT : T.IsPositive := (LinearMap.isPositive_toContinuousLinearMap_iff A).mpr hA
  change ‖T‖ ≤ c
  rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx, hc]
  have hden : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hlower : 0 ≤ T.reApplyInnerSelf x := hT.re_inner_nonneg_left x
  have hupper : T.reApplyInnerSelf x ≤ c * ‖x‖^2 := by
    have h := hdef.re_inner_nonneg_left x
    change 0 ≤ (inner ℂ ((c : ℂ) • x - A x) x).re at h
    rw [inner_sub_left, inner_smul_left, Complex.sub_re] at h
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero,
      show (inner ℂ x x).re = ‖x‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) x] at h
    exact sub_nonneg.mp h
  have hquot : T.rayleighQuotient x = T.reApplyInnerSelf x / ‖x‖^2 := rfl
  rw [hquot, abs_of_nonneg (div_nonneg hlower hden.le)]
  exact (div_le_iff₀ hden).mpr hupper
end QEC.Semantics.Davies
