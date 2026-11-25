-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.lower_of_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:47.596459+00:00
-- url     : https://prove2.me/submissions/5de066a7-48f4-48e4-a7f8-27f0b77a5229

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_VanishAtSStatementPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
  Filter Asymptotics
open scoped ENNReal
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf
theorem _root_.solution {n : ℕ} (hn : 0 < n) {σ : V n → V n} (h0 : σ 0 = 0)
    (hdet : (fderiv ℂ σ 0).det ≠ 0) : ∃ c > 0, ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ≤ ‖σ z‖ := by
  have hdiff : DifferentiableAt ℂ σ 0 := by
    by_contra hnd
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt hnd]
    simp [ContinuousLinearMap.det, LinearMap.det_zero, hn.ne']
  set L := fderiv ℂ σ 0 with hL
  have hu : IsUnit (L : V n →ₗ[ℂ] V n) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hbij : Function.Bijective (L : V n →ₗ[ℂ] V n) := (Module.End.isUnit_iff _).mp hu
  let e : V n ≃L[ℂ] V n := (LinearEquiv.ofBijective (L : V n →ₗ[ℂ] V n) hbij).toContinuousLinearEquiv
  set K : ℝ := ‖(e.symm : V n →L[ℂ] V n)‖ + 1 with hKdef
  have hK : 0 < K := by positivity
  have hle : ∀ z, ‖z‖ ≤ K * ‖L z‖ := by
    intro z
    have h1 : (e.symm : V n →L[ℂ] V n) (L z) = z := by
      have h2 : e z = L z := rfl
      rw [← h2, ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]
    calc ‖z‖ = ‖(e.symm : V n →L[ℂ] V n) (L z)‖ := by rw [h1]
      _ ≤ ‖(e.symm : V n →L[ℂ] V n)‖ * ‖L z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖L z‖ := by gcongr; linarith
  have hc0 : (0 : ℝ) < 1 / (2 * K) := by positivity
  have hcK : 1 / (2 * K) * K = 1 / 2 := by field_simp
  refine ⟨1 / (2 * K), hc0, ?_⟩
  have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hdiff.hasFDerivAt).def hc0
  filter_upwards [ho] with z hz
  simp only [zero_add, h0, sub_zero] at hz
  have h3 : ‖L z‖ ≤ ‖σ z‖ + ‖σ z - L z‖ := by
    have h4 := norm_sub_le (σ z) (σ z - L z)
    simpa using h4
  have h4 : 1 / (2 * K) * ‖z‖ ≤ 1 / (2 * K) * (K * ‖L z‖) := mul_le_mul_of_nonneg_left (hle z) hc0.le
  have h5 : 1 / (2 * K) * (K * ‖L z‖) = ‖L z‖ / 2 := by rw [← mul_assoc, hcK]; ring
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf
