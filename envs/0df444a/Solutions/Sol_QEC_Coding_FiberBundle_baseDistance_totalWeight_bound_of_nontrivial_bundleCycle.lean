-- Prove2me | solution 1 for QEC.Coding.FiberBundle.baseDistance_totalWeight_bound_of_nontrivial_bundleCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:02:00.061064+00:00
-- url     : https://prove2.me/submissions/04a59f35-8382-4e9c-9ef4-8196b7b4e349

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_homologyBaseProjection_le_horizontalComponent
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_le
import Theorems.Thm_QEC_Coding_FiberBundle_baseDistance_bound_of_nontrivial_bundleCycle

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDistance : RandomBase.HasLinearDistance baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleBoundaryCode.carrier) :
    4 * r ≤ 5 * HammingWeight z := by
  have hBase := baseDistance_bound_of_nontrivial_bundleCycle
    baseSample twistSample hRank hDistance z hz hzNontrivial
  have hProjectionHorizontal :=
    hammingWeight_homologyBaseProjection_le_horizontalComponent z
  have hHorizontalTotal := hammingWeight_horizontalComponent_le z
  omega
end QEC.Coding.FiberBundle
