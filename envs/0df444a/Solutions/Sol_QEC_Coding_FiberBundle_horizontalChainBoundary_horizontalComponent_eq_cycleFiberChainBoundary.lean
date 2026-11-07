-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:47:41.655208+00:00
-- url     : https://prove2.me/submissions/b7d7d4ed-0d13-4e4d-a12f-bef32f564a65

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_boundary1_apply_eq_horizontal_add_vertical

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
    (a : Fin (3 * r)) :
    horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a =
      cycleFiberChainBoundary (ell * ell) (verticalFiber z a) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  have hzZero : boundary1 D z = 0 :=
    ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  funext j
  have hj := congrFun hzZero (a, j)
  rw [boundary1_apply_eq_horizontal_add_vertical] at hj
  have hHorizontal :
      horizontalChainBoundary baseSample twistSample
          (horizontalComponent z) a j =
        -(∑ k : ZMod (ell * ell),
          D.fiberBoundary j k * z (Sum.inr (a, k))) := by
    apply eq_neg_of_add_eq_zero_left
    exact hj
  rw [hHorizontal, ZMod.neg_eq_self_mod_two]
  rfl
end QEC.Coding.FiberBundle
