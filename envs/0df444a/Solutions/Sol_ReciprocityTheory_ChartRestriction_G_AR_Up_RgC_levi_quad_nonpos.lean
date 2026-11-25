-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RgC.levi_quad_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:48.857576+00:00
-- url     : https://prove2.me/submissions/ba84bc5c-e6a1-49b4-bfc4-4871a3dd0ae2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgC_leviV_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgC_quad_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_ofReal_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
theorem _root_.solution {r s : ℕ} (τ : ℝ) (ℓ : Fin r → Fin s → V n → ℂ)
    (hℓ : ∀ a b, ContDiff ℂ ∞ (ℓ a b)) (x : V n) (ξ : Fin n → ℂ) :
    (leviV n (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) x ξ).re ≤ 0 := by
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun y => Complex.normSq (ℓ a b y)) x := by
    intro a b
    have h := quad_contDiff (r := 1) (s := 1) 0 (fun _ _ => ℓ a b) (fun _ _ => hℓ a b)
    have h2 : ContDiff ℝ ∞ (fun y => Complex.normSq (ℓ a b y)) := by
      have := h.neg
      simpa using this
    exact h2.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  have hca : ∀ a, ContDiffAt ℝ 2 (fun y => ∑ b, Complex.normSq (ℓ a b y)) x := fun a =>
    ContDiffAt.sum fun b _ => hc a b
  have hS : ContDiffAt ℝ 2 (fun y => ∑ a, ∑ b, Complex.normSq (ℓ a b y)) x :=
    ContDiffAt.sum fun a _ => hca a
  have e1 : (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) =
      fun y => ((τ + (-1) * ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ) := by
    funext y; push_cast; ring
  rw [e1, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add contDiffAt_const (contDiffAt_const.mul hS) ξ,
    leviV_const, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hS ξ,
    ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum hca ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum (fun b => hc _ b) ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.H.leviV_normSq_comp ((hℓ _ _).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)) ξ]
  simp only [zero_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum,
    Complex.im_sum, zero_mul, sub_zero]
  have : 0 ≤ ∑ a : Fin r, ∑ b : Fin s, Complex.normSq (∑ j, wd n j (ℓ a b) x * ξ j) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _
  nlinarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
