-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_veryLarge_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:09:49.795302+00:00
-- url     : https://prove2.me/submissions/f2f30787-e583-45ff-a426-7e4ce7fb5889

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exp_neg_six_le_one_over_343
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_le_expEnvelope


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (p : Real) (w : Nat) (hpHalf : p ≤ 1 / 2)
    (hlarge : 3 ≤ p * w) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤ (172 : Real) / 343 := by
  calc
    _ ≤ (1 + Real.exp (-2 * (p * w))) / 2 :=
      parityProbabilityBase_le_expEnvelope p w hpHalf
    _ ≤ (1 + Real.exp (-6)) / 2 := by
      gcongr
      nlinarith
    _ ≤ (1 + (1 : Real) / 343) / 2 := by
      gcongr
      exact exp_neg_six_le_one_over_343
    _ = _ := by norm_num
end QEC.Coding.FiberBundle.RandomBase
