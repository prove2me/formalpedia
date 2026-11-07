-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_le_of_pow_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:07.284015+00:00
-- url     : https://prove2.me/submissions/3a9071b6-2505-4e41-8b9a-1f2921dfd291

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound

set_option autoImplicit false
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {x r : ℝ} (hr : 0 < r)
    (h : (fun n : ℕ => |x| ^ n) =O[atTop]
      fun n : ℕ => r ^ n) :
    |x| ≤ r := by
  by_contra hxr
  have hrx : r < |x| := lt_of_not_ge hxr
  have hlittle : (fun n : ℕ => r ^ n) =o[atTop]
      fun n : ℕ => |x| ^ n :=
    isLittleO_pow_pow_of_lt_left hr.le hrx
  have hfrequent : ∃ᶠ n : ℕ in atTop, r ^ n ≠ 0 :=
    ((eventually_gt_atTop 0).mono fun n _hn =>
      pow_ne_zero n hr.ne').frequently
  exact hlittle.not_isBigO hfrequent h
end QEC.Coding.TannerLiftedProduct
