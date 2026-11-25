-- Prove2me | solution 1 for PI.EF.pTerm_le_far
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:54.517037+00:00
-- url     : https://prove2.me/submissions/50d87e91-6edf-40b1-828d-8018f7454332

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
import Theorems.Thm_PI_EF_abs_log_div_ge_far
import Theorems.Thm_PI_EF_kb_le_of_le
import Theorems.Thm_PI_EF_kb_nonneg
import Theorems.Thm_PI_EF_rpow_cLine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n) :
    pTerm u T n ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n := by
  have hu0 : 0 < u := by linarith
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : kb T (u / n) ≤ 4 / T := by
    have := kb_le_of_le hT (by norm_num : (0 : ℝ) < 1 / 2)
      (le_trans (by linarith [Real.log_two_gt_d9]) (abs_log_div_ge_far hu0 hx h))
    refine this.trans (le_of_eq ?_)
    field_simp
    norm_num
  have h2 : (u / n) ^ cLine u = Real.exp 1 * u * (n : ℝ) ^ (-cLine u) := by
    rw [Real.div_rpow hu0.le hx.le, Real.rpow_neg hx.le, rpow_cLine hu]
    rfl
  have h3 : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h4 : 0 ≤ (u / n) ^ cLine u := Real.rpow_nonneg (by positivity) _
  have h5 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  unfold pTerm logTerm
  calc ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)
      ≤ Real.log n * (u / n) ^ cLine u * (4 / T) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h3 h4) h1 (kb_nonneg hT _) (mul_nonneg h5 h4)
    _ = (4 * Real.exp 1 * u / T) * (Real.log n * (n : ℝ) ^ (-cLine u)) := by
        rw [h2]; ring
end PI.EF
