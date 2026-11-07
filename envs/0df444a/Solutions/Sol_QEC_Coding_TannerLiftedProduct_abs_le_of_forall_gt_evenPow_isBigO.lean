-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_le_of_forall_gt_evenPow_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:12:32.61159+00:00
-- url     : https://prove2.me/submissions/9978c2c9-a739-40d0-a432-5c2a33727f4e

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_pow_isBigO

set_option autoImplicit false
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {x r : ℝ} (hr : 0 ≤ r)
    (h : ∀ s : ℝ, r < s →
      (fun n : ℕ => |x| ^ (2 * n)) =O[atTop]
        fun n : ℕ => s ^ (2 * n)) :
    |x| ≤ r := by
  by_contra hxr
  have hrx : r < |x| := lt_of_not_ge hxr
  let s := (r + |x|) / 2
  have hrs : r < s := by
    dsimp [s]
    linarith
  have hsx : s < |x| := by
    dsimp [s]
    linarith
  have hs : 0 < s := hr.trans_lt hrs
  have hsq : 0 < s ^ 2 := sq_pos_of_pos hs
  have hO : (fun n : ℕ => (|x| ^ 2) ^ n) =O[atTop]
      fun n : ℕ => (s ^ 2) ^ n := by
    simpa [pow_mul] using h s hrs
  have hO' : (fun n : ℕ => |(|x| ^ 2)| ^ n) =O[atTop]
      fun n : ℕ => (s ^ 2) ^ n := by
    simpa [abs_of_nonneg (sq_nonneg |x|)] using hO
  have hle := abs_le_of_pow_isBigO (x := |x| ^ 2) hsq hO'
  rw [abs_of_nonneg (sq_nonneg |x|)] at hle
  nlinarith [sq_nonneg (|x| - s)]
end QEC.Coding.TannerLiftedProduct
