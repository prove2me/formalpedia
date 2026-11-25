-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RgA.grad_le_of_minorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:14.635273+00:00
-- url     : https://prove2.me/submissions/dbb61ff5-6aef-426a-8264-2c809b9efa90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviChain
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_re_nonpos_of_isLocalMax
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_ofReal_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviChain
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgA
open Topology Filter
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgA
theorem _root_.solution (rh Ψ : V n → ℝ) (v0 : V n) (C : ℝ) (hC : 0 < C)
    (hΨ0 : 0 < Ψ v0) (hrh : ContDiffAt ℝ 2 rh v0) (hΨ : ContDiffAt ℝ 2 Ψ v0) (ξ : Fin n → ℂ)
    (hL : (leviV n (fun y => (Ψ y : ℂ)) v0 ξ).re ≤ 0)
    (hle : ∀ᶠ v in 𝓝 v0, -C * Real.log (Ψ v) ≤ rh v) (heq : rh v0 = -C * Real.log (Ψ v0)) :
    Complex.normSq (∑ j, wd n j (fun y => (rh y : ℂ)) v0 * ξ j) ≤
      C * (leviV n (fun y => (rh y : ℂ)) v0 ξ).re := by
  set k : ℝ → ℝ := fun t => -C * Real.log t with hkdef
  set ψ : V n → ℝ := fun y => k (Ψ y) with hψdef
  have hk : ContDiffAt ℝ 2 k (Ψ v0) := contDiffAt_const.mul (Real.contDiffAt_log.2 hΨ0.ne')
  have hψ : ContDiffAt ℝ 2 ψ v0 := hk.comp v0 hΨ
  have hrd : DifferentiableAt ℝ rh v0 := hrh.differentiableAt (by simp)
  have hψd : DifferentiableAt ℝ ψ v0 := hψ.differentiableAt (by simp)
  have hΨd : DifferentiableAt ℝ Ψ v0 := hΨ.differentiableAt (by simp)
  have hkd : DifferentiableAt ℝ k (Ψ v0) := hk.differentiableAt (by simp)
  have hmin : IsLocalMin (fun y => rh y - ψ y) v0 := by
    filter_upwards [hle] with v hv
    simp only [hψdef, hkdef]
    linarith
  have hfd : fderiv ℝ rh v0 = fderiv ℝ ψ v0 := by
    have h := hmin.fderiv_eq_zero
    rw [fderiv_fun_sub hrd hψd] at h
    exact sub_eq_zero.1 h
  have hwd : ∀ j, wd n j (fun y => (rh y : ℂ)) v0 = wd n j (fun y => (ψ y : ℂ)) v0 := by
    intro j
    simp only [wd, fderiv_ofReal_apply hrd, fderiv_ofReal_apply hψd, hfd]
  have hdk : deriv k = fun t => -C * t⁻¹ := by
    funext t
    simp only [hkdef]
    rw [deriv_const_mul_field', Real.deriv_log']
  have hddk : deriv (deriv k) = fun t => C * (t ^ 2)⁻¹ := by
    rw [hdk]
    funext t
    rw [deriv_const_mul_field']
    show -C * deriv (fun x : ℝ => x⁻¹) t = _
    rw [deriv_inv]
    ring
  have hwdψ : ∀ j, wd n j (fun y => (ψ y : ℂ)) v0 =
      (((-C * (Ψ v0)⁻¹ : ℝ)) : ℂ) * wd n j (fun y => (Ψ y : ℂ)) v0 := by
    intro j
    rw [show (fun y => (ψ y : ℂ)) = fun y => (k (Ψ y) : ℂ) from rfl, wd_ofReal_comp hkd hΨd, hdk]
  have hchain := leviChain n k Ψ v0 ξ hΨ hk
  rw [hddk, hdk] at hchain

  have hmax : IsLocalMax (fun y => ψ y + (-1) * rh y) v0 := by
    have := hmin.neg
    refine this.congr ?_
    filter_upwards with y
    ring
  have hcd : ContDiffAt ℝ 2 (fun y => ψ y + (-1) * rh y) v0 := hψ.add (contDiffAt_const.mul hrh)
  have h2 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hcd hmax ξ
  rw [ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hψ (contDiffAt_const.mul hrh) ξ,
    ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hrh ξ] at h2
  have hψL : leviV n (fun y => (ψ y : ℂ)) v0 ξ = leviV n (fun y => (k (Ψ y) : ℂ)) v0 ξ := rfl
  rw [hψL, hchain] at h2
  set N := Complex.normSq (∑ j, wd n j (fun y => (Ψ y : ℂ)) v0 * ξ j) with hN
  set LΨ := (leviV n (fun y => (Ψ y : ℂ)) v0 ξ).re
  set Lr := (leviV n (fun y => (rh y : ℂ)) v0 ξ).re
  have h3 : (-C * (Ψ v0)⁻¹) * LΨ + C * ((Ψ v0) ^ 2)⁻¹ * N ≤ Lr := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.neg_re, Complex.one_re, neg_mul, one_mul] at h2
    linarith
  have hlhs : Complex.normSq (∑ j, wd n j (fun y => (rh y : ℂ)) v0 * ξ j) =
      (C * (Ψ v0)⁻¹) ^ 2 * N := by
    simp only [hwd, hwdψ, mul_assoc, ← Finset.mul_sum, Complex.normSq_mul, Complex.normSq_ofReal, hN]
    ring
  rw [hlhs]
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hi : 0 < (Ψ v0)⁻¹ := inv_pos.2 hΨ0
  have h4 : 0 ≤ (-C * (Ψ v0)⁻¹) * LΨ := by
    have : -C * (Ψ v0)⁻¹ ≤ 0 := by nlinarith
    nlinarith
  have h5 : (C * (Ψ v0)⁻¹) ^ 2 * N = C * (C * ((Ψ v0) ^ 2)⁻¹ * N) := by
    ring
  rw [h5]
  exact mul_le_mul_of_nonneg_left (by linarith) hC.le
end ReciprocityTheory.ChartRestriction.G.AR.Up.RgA
