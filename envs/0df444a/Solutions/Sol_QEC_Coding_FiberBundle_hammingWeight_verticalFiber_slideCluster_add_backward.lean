-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_verticalFiber_slideCluster_add_backward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:14:51.683327+00:00
-- url     : https://prove2.me/submissions/f290990b-1f32-4d4d-9ec6-83569b30ee5c

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalChainBoundary_cluster_eq_cycleFiberChainBoundary_of_ne_zero
import Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_oneStepSlide
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_forward_add_backward_cycle_toggles

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
        (verticalFiber z a +
          backwardVertexToggle (ell * ell)
            (horizontalChainBoundary baseSample twistSample
              (horizontalClusterSubchain
                baseSample twistSample z root) a)) =
      2 * HammingWeight (verticalFiber z a) := by
  rw [verticalFiber_oneStepSlide]
  apply hammingWeight_forward_add_backward_cycle_toggles
    (ell * ell) (by
      have hEll : 2 ≤ ell := by
        have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
        omega
      nlinarith)
  intro j hgj
  exact
    horizontalChainBoundary_cluster_eq_cycleFiberChainBoundary_of_ne_zero
      baseSample twistSample z hz root a j hgj
end QEC.Coding.FiberBundle
