-- Prove2me | solution 1 for QEC.Coding.FiberBundle.negativeStepSlide_mem_middleBoundaryCode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:10:10.771319+00:00
-- url     : https://prove2.me/submissions/32443afc-f6fd-4f51-984a-5d1de2da665b

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives

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
    negativeStepSlide baseSample twistSample z h ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let c := negativeStepSlideTwoChain (ell * ell) h
  have hc : boundary2 D c ∈
      (chainComplex D).middleBoundaryCode.carrier :=
    ((chainComplex D).mem_middleBoundaryCode_iff
      (boundary2 D c)).2 ⟨c, rfl⟩
  change z + boundary2 D c ∈
      (chainComplex D).middleBoundaryCode.carrier ↔
    z ∈ (chainComplex D).middleBoundaryCode.carrier
  exact (chainComplex D).middleBoundaryCode.carrier.add_mem_iff_left hc
end QEC.Coding.FiberBundle
