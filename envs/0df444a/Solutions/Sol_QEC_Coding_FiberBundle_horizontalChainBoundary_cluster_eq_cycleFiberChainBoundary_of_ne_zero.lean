-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalChainBoundary_cluster_eq_cycleFiberChainBoundary_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:09:39.524551+00:00
-- url     : https://prove2.me/submissions/c80d4221-404e-4b6c-8193-573e97213301

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalChainBoundary_cluster_eq_horizontalComponent_of_ne_zero

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
    (a : Fin (3 * r)) (j : ZMod (ell * ell))
    (hg :
      horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j ≠ 0) :
    horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j =
      cycleFiberChainBoundary (ell * ell) (verticalFiber z a) j := by
  rw [horizontalChainBoundary_cluster_eq_horizontalComponent_of_ne_zero
    baseSample twistSample z root a j hg]
  exact congrFun
    (horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
      baseSample twistSample z hz a) j
end QEC.Coding.FiberBundle
