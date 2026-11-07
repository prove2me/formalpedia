-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_negativeStepSlide_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:35.776694+00:00
-- url     : https://prove2.me/submissions/7986b3ce-494b-4f27-8ed7-5cffb7f2679c

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_add_subword_add_hammingWeight
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_backwardShiftHorizontalSubchain
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalComponent_negativeStepSlide
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


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
    (hhz : IsBinarySubword h (horizontalComponent z)) :
    HammingWeight
        (horizontalComponent
          (negativeStepSlide baseSample twistSample z h)) ≤
      HammingWeight (horizontalComponent z) := by
  rw [horizontalComponent_negativeStepSlide]
  calc
    HammingWeight
        ((horizontalComponent z + h) +
          backwardShiftHorizontalSubchain (ell * ell) h) ≤
        HammingWeight (horizontalComponent z + h) +
          HammingWeight
            (backwardShiftHorizontalSubchain (ell * ell) h) :=
      HammingWeight_add_le _ _
    _ = HammingWeight (horizontalComponent z + h) +
          HammingWeight h := by
      rw [hammingWeight_backwardShiftHorizontalSubchain]
    _ = HammingWeight (horizontalComponent z) :=
      hammingWeight_add_subword_add_hammingWeight h
        (horizontalComponent z) hhz
end QEC.Coding.FiberBundle
