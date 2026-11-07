-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalComponent_oneStepSlide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:53:13.880694+00:00
-- url     : https://prove2.me/submissions/0ed0fa08-ddee-4484-88d4-e35aec6c8f03

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_boundary2_oneStepSlideTwoChain

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
      (Fin (4 * r) × ZMod (ell * ell))) :
    horizontalComponent
        (oneStepSlide baseSample twistSample z h) =
      (horizontalComponent z + h) +
        shiftHorizontalSubchain (ell * ell) h := by
  funext bi
  rcases bi with ⟨b, i⟩
  change horizontalFiber
      (oneStepSlide baseSample twistSample z h) b i =
    ((horizontalComponent z + h) +
      shiftHorizontalSubchain (ell * ell) h) (b, i)
  rw [oneStepSlide, show horizontalFiber
      (z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h)) b i =
      horizontalFiber z b i +
        horizontalFiber
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (oneStepSlideTwoChain h)) b i by rfl]
  rw [horizontalFiber_boundary2_oneStepSlideTwoChain]
  change z (Sum.inl (b, i)) + (h (b, i) + h (b, i - 1)) =
    (z (Sum.inl (b, i)) + h (b, i)) + h (b, i - 1)
  abel
end QEC.Coding.FiberBundle
