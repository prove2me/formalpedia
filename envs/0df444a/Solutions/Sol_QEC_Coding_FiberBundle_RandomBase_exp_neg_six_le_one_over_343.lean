-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.exp_neg_six_le_one_over_343
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:07:46.723873+00:00
-- url     : https://prove2.me/submissions/82ac12db-1ba2-4993-b306-17a21fa6573b

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exp_neg_two_le_one_seventh


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution :
    Real.exp (-6) ≤ (1 : Real) / 343 := by
  calc
    Real.exp (-6) = (Real.exp (-2)) ^ 3 := by
      rw [show (-6 : Real) = (3 : Nat) * (-2 : Real) by norm_num,
        Real.exp_nat_mul]
    _ ≤ ((1 : Real) / 7) ^ 3 := by
      exact pow_le_pow_left₀ (Real.exp_pos (-2)).le
        exp_neg_two_le_one_seventh 3
    _ = _ := by norm_num
end QEC.Coding.FiberBundle.RandomBase
