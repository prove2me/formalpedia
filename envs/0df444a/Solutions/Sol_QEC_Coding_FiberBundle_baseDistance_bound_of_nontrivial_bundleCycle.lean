-- Prove2me | solution 1 for QEC.Coding.FiberBundle.baseDistance_bound_of_nontrivial_bundleCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:23.940653+00:00
-- url     : https://prove2.me/submissions/b804e69e-ad2b-49bb-a32e-2e9ba75667d9

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_not_mem_middleBoundaryCode_iff_projection_ne_zero
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_mem_randomBaseCode_of_bundleCycle

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
    4 * r ≤ 5 * HammingWeight (homologyBaseProjection z) := by
  exact hDistance
    (homologyBaseProjection z)
    (homologyBaseProjection_mem_randomBaseCode_of_bundleCycle
      baseSample twistSample z hz)
    ((not_mem_middleBoundaryCode_iff_projection_ne_zero
      baseSample twistSample hRank z hz).1 hzNontrivial)
end QEC.Coding.FiberBundle
