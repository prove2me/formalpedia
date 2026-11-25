-- Prove2me | solution 1 for PI.EF.PK.line_bound_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:42.248537+00:00
-- url     : https://prove2.me/submissions/374ebe82-a8eb-496e-b8b3-c909bed42e32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Theorems.Thm_PI_EF_PK_horiz_bound
import Theorems.Thm_PI_EF_PK_vert_bound
import Theorems.Thm_PI_EF_PK_rectInt_eq_zero
import Theorems.Thm_PI_EF_PK_far_side_small
import Theorems.Thm_PI_EF_PK_three_sides

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (l c T : ℝ) (hl : l < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)‖ ≤ 2 * (Real.exp (l * c) / (-l) / T) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  set U := max (c + 1) (2 * T / ε) with hU
  have hcU : c < U := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hU0 : 0 < U := by linarith
  have hUe : 2 * T / ε ≤ U := le_max_right _ _
  have hdiff : DifferentiableOn ℂ (ker l) (Set.uIcc c U ×ℂ Set.uIcc (-T) T) := by
    intro z hz
    have hzre : z.re ∈ Set.uIcc c U := hz.1
    rw [Set.uIcc_of_le hcU.le] at hzre
    have hz0 : z ≠ 0 := by
      intro h
      have h1 : c ≤ z.re := hzre.1
      rw [h, Complex.zero_re] at h1
      linarith
    apply DifferentiableAt.differentiableWithinAt
    unfold ker
    exact DifferentiableAt.div (by fun_prop) differentiableAt_id hz0
  have hrect := rectInt_eq_zero (ker l) c U (-T) T hdiff
  unfold rectInt at hrect
  rw [smul_eq_mul, smul_eq_mul] at hrect
  have hB := horiz_bound l c U (-T) hl.ne (by linarith) hcU.le
  have hTp := horiz_bound l c U T hl.ne hT.ne' hcU.le
  rw [abs_neg, abs_of_pos hT] at hB
  rw [abs_of_pos hT] at hTp
  have hR := (vert_bound l U T hU0.ne' hT.le).trans
    (far_side_small l U U T ε (mul_neg_of_neg_of_pos hl hU0).le (abs_of_pos hU0) hT hε hU0 hUe)
  have hL : I * (∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)) =
      (∫ x : ℝ in c..U, ker l ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in c..U, ker l ((x : ℂ) + T * I))
        + I * ∫ t : ℝ in -T..T, ker l ((U : ℂ) + t * I) := by
    linear_combination -1 * hrect
  have h3 := three_sides hL
  have hmono : (Real.exp (l * U) - Real.exp (l * c)) / l / T ≤ Real.exp (l * c) / (-l) / T := by
    rw [show (Real.exp (l * U) - Real.exp (l * c)) / l = (Real.exp (l * c) - Real.exp (l * U)) / (-l) by ring]
    apply div_le_div_of_nonneg_right _ hT.le
    apply div_le_div_of_nonneg_right _ (by linarith)
    linarith [Real.exp_pos (l * U)]
  linarith
end PI.EF.PK
