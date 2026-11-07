-- Prove2me | solution 1 for QEC.Coding.FiberBundle.oneStepSlide_mem_middleBoundaryCode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:09:43.390405+00:00
-- url     : https://prove2.me/submissions/9e54207a-c68d-4015-a5cd-5ed9e00530e1

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
    oneStepSlide baseSample twistSample z h ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let c := oneStepSlideTwoChain h
  constructor
  · intro hSlide
    rcases ((chainComplex D).mem_middleBoundaryCode_iff
      (oneStepSlide baseSample twistSample z h)).1 hSlide with
      ⟨d, hd⟩
    apply ((chainComplex D).mem_middleBoundaryCode_iff z).2
    refine ⟨c + d, ?_⟩
    change boundary2 D (c + d) = z
    rw [map_add]
    have hd' : boundary2 D d = z + boundary2 D c := by
      exact hd
    rw [hd']
    funext q
    let w := boundary2 D c q
    change w + (z q + w) = z q
    have hww : w + w = 0 := by
      calc
        w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel w
    calc
      w + (z q + w) = z q + (w + w) := by abel
      _ = z q := by rw [hww, add_zero]
  · intro hzBoundary
    rcases ((chainComplex D).mem_middleBoundaryCode_iff z).1
      hzBoundary with ⟨d, hd⟩
    apply ((chainComplex D).mem_middleBoundaryCode_iff
      (oneStepSlide baseSample twistSample z h)).2
    refine ⟨d + c, ?_⟩
    change boundary2 D (d + c) =
      oneStepSlide baseSample twistSample z h
    have hd' : boundary2 D d = z := hd
    rw [map_add, hd']
    rfl
end QEC.Coding.FiberBundle
