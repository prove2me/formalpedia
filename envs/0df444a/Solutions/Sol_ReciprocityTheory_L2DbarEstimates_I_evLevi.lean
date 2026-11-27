-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evLevi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:42:25.726324+00:00
-- url     : https://prove2.me/submissions/f86cb606-fd9a-47e8-881f-da11ae3800cb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLevi
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_contDiff_exp_neg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_alg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_cs
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_expNeg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_sumSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_levi_expNeg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_levi_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_levi_sumSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_smoothR_sumSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_const_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff ComplexConjugate
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (M : Type u) [TopologicalSpace M] : EvLeviStatement n M := by
  intro z g ph r _ hg hph hr x ξ
  have hS : SmoothR n z (fun y => ∑ i, ‖g i y‖ ^ 2) := evl_smoothR_sumSq n z Finset.univ g hg
  have hE : SmoothR n z (fun y => Real.exp (-ph y)) := SmoothR.comp n z _ contDiff_exp_neg ph hph
  have hSE : SmoothR n z (fun y => (∑ i, ‖g i y‖ ^ 2) * Real.exp (-ph y)) :=
    SmoothR.mul n z _ _ hS hE
  have hev : ev n g ph r = fun y => (r ^ 2)⁻¹ * ((∑ i, ‖g i y‖ ^ 2) * Real.exp (-ph y)) := by
    funext y; unfold ev; ring
  have hvx : ev n g ph r x = (r ^ 2)⁻¹ * ((∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x)) := by
    rw [hev]
  have hLev : Levi n z (ev n g ph r) x ξ = (((r ^ 2)⁻¹ : ℝ) : ℂ) *
      Levi n z (fun y => (∑ i, ‖g i y‖ ^ 2) * Real.exp (-ph y)) x ξ := by
    rw [hev]; exact levi_const_mul n z _ _ (SmoothR.ckR n z 2 _ hSE) x ξ
  have hLSE : Levi n z (fun y => (∑ i, ‖g i y‖ ^ 2) * Real.exp (-ph y)) x ξ =
      Levi n z (fun y => ∑ i, ‖g i y‖ ^ 2) x ξ * ((Real.exp (-ph x) : ℝ) : ℂ) +
        ((∑ i, ‖g i x‖ ^ 2 : ℝ) : ℂ) * Levi n z (fun y => Real.exp (-ph y)) x ξ +
        conj (dDot n z (fun y => ((∑ i, ‖g i y‖ ^ 2 : ℝ) : ℂ)) x ξ) *
          dDot n z (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x ξ +
        dDot n z (fun y => ((∑ i, ‖g i y‖ ^ 2 : ℝ) : ℂ)) x ξ *
          conj (dDot n z (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x ξ) :=
    evl_levi_mul n z _ _ (SmoothR.ckR n z 2 _ hS) (SmoothR.ckR n z 2 _ hE) x ξ
  rw [evl_levi_sumSq n z Finset.univ g hg x ξ, evl_levi_expNeg n z ph hph x ξ,
    evl_dDot_sumSq n z Finset.univ g hg x ξ, evl_dDot_expNeg n z ph hph x ξ] at hLSE
  have hdev : dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ = (((r ^ 2)⁻¹ : ℝ) : ℂ) *
      ((∑ i, conj (g i x) * dDot n z (g i) x ξ) * ((Real.exp (-ph x) : ℝ) : ℂ) +
        ((∑ i, ‖g i x‖ ^ 2 : ℝ) : ℂ) *
          (-((Real.exp (-ph x) : ℝ) : ℂ) * dDot n z (fun y => (ph y : ℂ)) x ξ)) := by
    have hf : (fun y => (ev n g ph r y : ℂ)) = fun y => (((r ^ 2)⁻¹ : ℝ) : ℂ) *
        (((∑ i, ‖g i y‖ ^ 2 : ℝ) : ℂ) * ((Real.exp (-ph y) : ℝ) : ℂ)) := by
      funext y; rw [hev]; simp only [Complex.ofReal_mul]
    rw [hf, evl_dDot_const_mul n z _ _ (Ck.mul n z 1 _ _ (SmoothR.ckR n z 1 _ hS)
      (SmoothR.ckR n z 1 _ hE)) x ξ, evl_dDot_mul n z _ _ (SmoothR.ckR n z 1 _ hS)
      (SmoothR.ckR n z 1 _ hE) x ξ, evl_dDot_sumSq n z Finset.univ g hg x ξ,
      evl_dDot_expNeg n z ph hph x ξ]
  have hCS := evl_cs Finset.univ (fun i => g i x) (fun i => dDot n z (g i) x ξ)
  generalize hP : ∑ i, conj (g i x) * dDot n z (g i) x ξ = P at hLSE hdev hCS
  generalize hb : dDot n z (fun y => (ph y : ℂ)) x ξ = b at hLSE hdev
  generalize hL : Levi n z ph x ξ = Lp at hLSE ⊢
  generalize hSx : ∑ i, ‖g i x‖ ^ 2 = Sx at hLSE hdev hCS hvx
  generalize hQ : ∑ i, ‖dDot n z (g i) x ξ‖ ^ 2 = Q at hLSE hCS
  have hSx0 : 0 ≤ Sx := hSx ▸ Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQ0 : 0 ≤ Q := hQ ▸ Finset.sum_nonneg fun i _ => sq_nonneg _
  have hN : ‖dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 =
      ((r ^ 2)⁻¹) ^ 2 * Real.exp (-ph x) ^ 2 *
        ((P.re - Sx * b.re) ^ 2 + (P.im - Sx * b.im) ^ 2) := by
    rw [hdev, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hR : (Levi n z (ev n g ph r) x ξ).re = (r ^ 2)⁻¹ * (Q * Real.exp (-ph x) +
      Sx * (Real.exp (-ph x) * (b.re ^ 2 + b.im ^ 2 - Lp.re)) -
      2 * Real.exp (-ph x) * (P.re * b.re + P.im * b.im)) := by
    rw [hLev, hLSE]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, map_mul, map_neg, Complex.conj_ofReal]
    ring
  rw [hN, hR, hvx]
  rw [Complex.sq_norm, Complex.normSq_apply] at hCS
  exact evl_alg _ _ Sx Q P.re P.im b.re b.im Lp.re (by positivity) (Real.exp_pos _) hSx0 hQ0
    (by nlinarith [hCS])
end ReciprocityTheory.L2DbarEstimates.I
