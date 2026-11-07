-- Prove2me | solution 1 for QEC.Coding.FiberBundle.cohomologyDistanceAtLeast_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:01:39.185201+00:00
-- url     : https://prove2.me/submissions/9056df3b-28f1-493f-8a99-fa73a76e5192

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_cohomologyDistanceAtLeast_of_numeric_bounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample) :
    CohomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample)
      (min
        (Fintype.card (ZMod (ell * ell)) / 2)
        ((6 * r) / (100000 * Delta))) := by
  apply cohomologyDistanceAtLeast_of_numeric_bounds
    baseSample twistSample hRank hDelta hDegree hExpansion
  · calc
      2 * min
          (Fintype.card (ZMod (ell * ell)) / 2)
          ((6 * r) / (100000 * Delta)) ≤
        2 * (Fintype.card (ZMod (ell * ell)) / 2) := by
          exact Nat.mul_le_mul_left 2 (min_le_left _ _)
      _ ≤ Fintype.card (ZMod (ell * ell)) := Nat.mul_div_le _ _
  · calc
      100000 * Delta *
          min
            (Fintype.card (ZMod (ell * ell)) / 2)
            ((6 * r) / (100000 * Delta)) ≤
        100000 * Delta * ((6 * r) / (100000 * Delta)) := by
          exact Nat.mul_le_mul_left _ (min_le_right _ _)
      _ ≤ 6 * r := Nat.mul_div_le _ _
end QEC.Coding.FiberBundle
