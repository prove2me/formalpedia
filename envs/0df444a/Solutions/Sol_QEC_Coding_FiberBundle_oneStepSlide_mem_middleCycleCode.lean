-- Prove2me | solution 1 for QEC.Coding.FiberBundle.oneStepSlide_mem_middleCycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:09:41.941219+00:00
-- url     : https://prove2.me/submissions/5ecd4141-6483-4af9-be0a-d2025ccd6b13

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
      (Fin (4 * r) × ZMod (ell * ell)))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier) :
    oneStepSlide baseSample twistSample z h ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  rw [(chainComplex D).mem_middleCycleCode_iff]
  rw [oneStepSlide, map_add]
  have hzZero := ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  rw [hzZero, zero_add]
  have hsquare := congrArg
    (fun f : Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell))) →ₗ[ZMod 2]
        Word (ZMod 2)
          (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
      f (oneStepSlideTwoChain h))
    (boundary_squared D)
  exact hsquare
end QEC.Coding.FiberBundle
