-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalFiber_add_primitiveBoundary_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:06:26.125004+00:00
-- url     : https://prove2.me/submissions/3e869630-acce-478d-8270-06a46db34047

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_boundary2_horizontalFiberPrimitiveTwoChain

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
    (hzProjection : homologyBaseProjection z = 0)
    (b : Fin (4 * r)) :
    horizontalFiber
        (z +
          boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (horizontalFiberPrimitiveTwoChain z)) b = 0 := by
  rw [show horizontalFiber
      (z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (horizontalFiberPrimitiveTwoChain z)) b =
      horizontalFiber z b +
        horizontalFiber
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (horizontalFiberPrimitiveTwoChain z)) b by rfl]
  rw [horizontalFiber_boundary2_horizontalFiberPrimitiveTwoChain
    baseSample twistSample z hzProjection b]
  funext i
  change horizontalFiber z b i + horizontalFiber z b i = 0
  calc
    horizontalFiber z b i + horizontalFiber z b i =
        horizontalFiber z b i + (-(horizontalFiber z b i)) := by
      rw [ZMod.neg_eq_self_mod_two]
    _ = 0 := add_neg_cancel (horizontalFiber z b i)
end QEC.Coding.FiberBundle
