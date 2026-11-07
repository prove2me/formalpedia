-- Prove2me | solution 1 for QEC.Coding.FiberBundle.cohomologyDistanceAtLeast_of_numeric_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:03.256382+00:00
-- url     : https://prove2.me/submissions/a0aee631-061c-47bf-9fea-718fecb91b05

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_cohomologyWeightAlternative

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell Delta d : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (hFiber : 2 * d ≤ Fintype.card (ZMod (ell * ell)))
    (hBase : 100000 * Delta * d ≤ 6 * r) :
    CohomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample) d := by
  intro z hz hzNontrivial
  rcases cohomologyWeightAlternative
      baseSample twistSample hRank hDelta hDegree hExpansion
      z hz hzNontrivial with hFiberWeight | hBaseWeight
  · omega
  · have hCoefficient : 0 < 100000 * Delta := by omega
    have hScaled :
        100000 * Delta * d <
          100000 * Delta * HammingWeight z :=
      hBase.trans_lt hBaseWeight
    have hdlt : d < HammingWeight z := by
      exact (Nat.mul_lt_mul_left hCoefficient).mp hScaled
    exact hdlt.le
end QEC.Coding.FiberBundle
