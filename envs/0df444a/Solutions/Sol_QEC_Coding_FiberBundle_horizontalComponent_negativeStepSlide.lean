-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalComponent_negativeStepSlide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:09:37.874588+00:00
-- url     : https://prove2.me/submissions/c1fa1b4c-040d-41ef-9cb1-49ddb12098ce

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_boundary2_negativeStepSlideTwoChain

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
        (negativeStepSlide baseSample twistSample z h) =
      (horizontalComponent z + h) +
        backwardShiftHorizontalSubchain (ell * ell) h := by
  funext bi
  rcases bi with ⟨b, i⟩
  change horizontalFiber
      (negativeStepSlide baseSample twistSample z h) b i =
    ((horizontalComponent z + h) +
      backwardShiftHorizontalSubchain (ell * ell) h) (b, i)
  rw [negativeStepSlide, show horizontalFiber
      (z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (negativeStepSlideTwoChain (ell * ell) h)) b i =
      horizontalFiber z b i +
        horizontalFiber
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (negativeStepSlideTwoChain (ell * ell) h)) b i by rfl]
  rw [horizontalFiber_boundary2_negativeStepSlideTwoChain]
  change z (Sum.inl (b, i)) + (h (b, i + 1) + h (b, i)) =
    (z (Sum.inl (b, i)) + h (b, i)) + h (b, i + 1)
  abel
end QEC.Coding.FiberBundle
