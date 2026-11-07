-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_verticalFiber_positive_add_negative_slideCluster
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:29.051848+00:00
-- url     : https://prove2.me/submissions/fd14312b-11b6-40d6-ae3e-9c87c54c454c

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_negativeStepSlide
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalFiber_slideCluster_add_backward

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell))
    (a : Fin (3 * r)) :
    HammingWeight
        (verticalFiber
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) a) +
      HammingWeight
        (verticalFiber
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) a) =
      2 * HammingWeight (verticalFiber z a) := by
  rw [verticalFiber_negativeStepSlide]
  exact hammingWeight_verticalFiber_slideCluster_add_backward
    baseSample twistSample z hz root a
end QEC.Coding.FiberBundle
