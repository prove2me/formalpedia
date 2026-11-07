-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_le_of_forall_gt_pow_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:13.390571+00:00
-- url     : https://prove2.me/submissions/e243e76e-83a7-4a3e-b924-f14f804e26e1

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
      (fun n : ℕ => |x| ^ n) =O[atTop]
        fun n : ℕ => s ^ n) :
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
  exact (not_le_of_gt hsx) (abs_le_of_pow_isBigO hs (h s hrs))
end QEC.Coding.TannerLiftedProduct
