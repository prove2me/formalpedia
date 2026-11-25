-- Prove2me | solution 1 for PI.EF.PK.line_bound_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:23.345399+00:00
-- url     : https://prove2.me/submissions/a84b59ce-6393-41c6-a136-255f6d2a333e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Theorems.Thm_PI_EF_PK_horiz_bound
import Theorems.Thm_PI_EF_PK_vert_bound
import Theorems.Thm_PI_EF_PK_far_side_small
import Theorems.Thm_PI_EF_PK_three_sides
import Theorems.Thm_PI_EF_PK_rectInt_ker

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
theorem _root_.solution (l c T : ℝ) (hl : 0 < l) (hc : 0 < c) (hT : 0 < T) :
    ‖(∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)) - 2 * π‖ ≤ 2 * (Real.exp (l * c) / l / T) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  set U := max 1 (2 * T / ε) with hU
  have hU0 : 0 < U := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hUe : 2 * T / ε ≤ U := le_max_right _ _
  have hrect := rectInt_ker l (-U) c (-T) T (by linarith) hc (by linarith) hT
  unfold rectInt at hrect
  rw [smul_eq_mul, smul_eq_mul] at hrect
  have hB := horiz_bound l (-U) c (-T) hl.ne' (by linarith) (by linarith)
  have hTp := horiz_bound l (-U) c T hl.ne' hT.ne' (by linarith)
  rw [abs_neg, abs_of_pos hT] at hB
  rw [abs_of_pos hT] at hTp
  have hR := (vert_bound l (-U) T (neg_ne_zero.2 hU0.ne') hT.le).trans
    (far_side_small l (-U) U T ε (by nlinarith) (by rw [abs_neg, abs_of_pos hU0]) hT hε hU0 hUe)
  have hL : I * ((∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)) - 2 * (π : ℂ)) =
      (∫ x : ℝ in -U..c, ker l ((x : ℂ) + T * I)) - (∫ x : ℝ in -U..c, ker l ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        + I * ∫ t : ℝ in -T..T, ker l (((-U : ℝ) : ℂ) + t * I) := by
    linear_combination hrect
  have h3 := three_sides hL
  have hmono : (Real.exp (l * c) - Real.exp (l * -U)) / l / T ≤ Real.exp (l * c) / l / T := by
    apply div_le_div_of_nonneg_right _ hT.le
    apply div_le_div_of_nonneg_right _ hl.le
    linarith [Real.exp_pos (l * -U)]
  linarith
end PI.EF.PK
