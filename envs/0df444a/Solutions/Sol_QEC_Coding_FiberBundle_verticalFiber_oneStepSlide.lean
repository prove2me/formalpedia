-- Prove2me | solution 1 for QEC.Coding.FiberBundle.verticalFiber_oneStepSlide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:08:14.377+00:00
-- url     : https://prove2.me/submissions/b2597353-420a-4e31-af7e-1226ffbc184d

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_boundary2_oneStepSlideTwoChain

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
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) :
    verticalFiber
        (oneStepSlide baseSample twistSample z h) a =
      verticalFiber z a +
        horizontalChainBoundary baseSample twistSample h a := by
  funext j
  change
    verticalFiber z a j +
        verticalFiber
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (oneStepSlideTwoChain h)) a j =
      verticalFiber z a j +
        horizontalChainBoundary baseSample twistSample h a j
  rw [verticalFiber_boundary2_oneStepSlideTwoChain]
  rfl
end QEC.Coding.FiberBundle
