-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalFiber_boundary2_oneStepSlideTwoChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:50:31.717063+00:00
-- url     : https://prove2.me/submissions/91b8e6a9-06e6-4cff-8fb5-73ac38cbb0f8

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_boundary2
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberChainBoundary_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (b : Fin (4 * r)) (i : ZMod (ell * ell)) :
    horizontalFiber
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h)) b i =
      h (b, i) + h (b, i - 1) := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  rw [horizontalFiber_boundary2]
  change cycleFiberChainBoundary (ell * ell) (fun j => h (b, j)) i =
    h (b, i) + h (b, i - 1)
  exact cycleFiberChainBoundary_apply (ell * ell) (by nlinarith) _ i
end QEC.Coding.FiberBundle
