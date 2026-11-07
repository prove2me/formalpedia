-- Prove2me | solution 1 for QEC.Coding.FiberBundle.globalSlideIterate_add_mem_middleBoundaryCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:11:49.957234+00:00
-- url     : https://prove2.me/submissions/ee94f8a7-4084-4b4b-a22a-5c1fad715e7f

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
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    ∀ k,
      globalSlideIterate baseSample twistSample z k + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  intro k
  induction k with
  | zero =>
      have hzz : z + z = 0 := by
        funext q
        calc
          z q + z q = z q + (-z q) := by
            rw [ZMod.neg_eq_self_mod_two]
          _ = 0 := add_neg_cancel _
      rw [globalSlideIterate, hzz]
      exact Submodule.zero_mem _
  | succ k ih =>
      let D := RandomTwist.fiberBundleData baseSample twistSample
      let current := globalSlideIterate baseSample twistSample z k
      let c := oneStepSlideTwoChain (horizontalComponent current)
      have hc : boundary2 D c ∈
          (chainComplex D).middleBoundaryCode.carrier :=
        ((chainComplex D).mem_middleBoundaryCode_iff
          (boundary2 D c)).2 ⟨c, rfl⟩
      have heq :
          globalSlideIterate baseSample twistSample z (k + 1) + z =
            (current + z) + boundary2 D c := by
        rw [globalSlideIterate]
        change (current + boundary2 D c) + z =
          (current + z) + boundary2 D c
        funext q
        change (current q + boundary2 D c q) + z q =
          (current q + z q) + boundary2 D c q
        abel
      rw [heq]
      exact Submodule.add_mem _ ih hc
end QEC.Coding.FiberBundle
