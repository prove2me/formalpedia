-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_log_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:31.219132+00:00
-- url     : https://prove2.me/submissions/972093bd-a452-40d4-84b4-372ba77c92b3

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_ReciprocityTheory_Cheb_log_norm_eq_sum
import Theorems.Thm_ReciprocityTheory_Cheb_normAtPlace_add_pos
import Theorems.Thm_ReciprocityTheory_Cheb_abs_log_normAtPlace_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
variable {y k : mixedSpace E} {B a : ℝ}
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) :
    |Real.log (mixedEmbedding.norm (y + k)) - Real.log (mixedEmbedding.norm y)| ≤
      (Module.finrank ℚ E : ℝ) * (2 * B / a) := by
  have ha0 : 0 < a := by linarith
  rw [log_norm_eq_sum (fun w => (normAtPlace_add_pos hB hk ha hy w).ne'),
    log_norm_eq_sum (fun w => (lt_of_lt_of_le ha0 (hy w)).ne'), ← Finset.sum_sub_distrib]
  calc |∑ w, ((mult w : ℝ) * Real.log (normAtPlace w (y + k)) - (mult w : ℝ) * Real.log (normAtPlace w y))|
      ≤ ∑ w, |(mult w : ℝ) * Real.log (normAtPlace w (y + k)) - (mult w : ℝ) * Real.log (normAtPlace w y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : InfinitePlace E, (mult w : ℝ) * (2 * B / a) := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (abs_log_normAtPlace_sub_le hB hk ha hy w) (Nat.cast_nonneg _)
    _ = (Module.finrank ℚ E : ℝ) * (2 * B / a) := by
        rw [← Finset.sum_mul, ← sum_mult_eq]; push_cast; ring
end ReciprocityTheory.Cheb
