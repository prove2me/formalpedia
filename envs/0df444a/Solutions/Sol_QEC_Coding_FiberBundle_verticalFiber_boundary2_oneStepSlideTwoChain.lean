-- Prove2me | solution 1 for QEC.Coding.FiberBundle.verticalFiber_boundary2_oneStepSlideTwoChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:50:33.782209+00:00
-- url     : https://prove2.me/submissions/b48e9e07-8b90-4047-a184-5e972f53303a

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_boundary2_apply_vertical

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
    (a : Fin (3 * r)) (j : ZMod (ell * ell)) :
    verticalFiber
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h)) a j =
      ∑ b : Fin (4 * r),
        RandomBase.boundary baseSample a b *
          h (b,
            (((RandomTwist.fiberBundleData baseSample twistSample
              ).connection b a).onOne.symm) j) := by
  change boundary2
      (RandomTwist.fiberBundleData baseSample twistSample)
      (oneStepSlideTwoChain h) (Sum.inr (a, j)) = _
  rw [boundary2_apply_vertical]
  rfl
end QEC.Coding.FiberBundle
