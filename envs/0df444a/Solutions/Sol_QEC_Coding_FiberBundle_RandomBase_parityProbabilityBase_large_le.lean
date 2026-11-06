-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_large_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:33:53.423471+00:00
-- url     : https://prove2.me/submissions/cb7c77c5-d2e4-4bae-935e-b2e50469081f

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_le_expEnvelope
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exp_neg_two_le_one_seventh

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (p : Real) (w : Nat) (hpHalf : p ≤ 1 / 2)
    (hlarge : 1 ≤ p * w) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤ (4 : Real) / 7 := by
  calc
    _ ≤ (1 + Real.exp (-2 * (p * w))) / 2 :=
      parityProbabilityBase_le_expEnvelope p w hpHalf
    _ ≤ (1 + Real.exp (-2)) / 2 := by
      gcongr
      nlinarith
    _ ≤ (1 + (1 : Real) / 7) / 2 := by
      gcongr
      exact exp_neg_two_le_one_seventh
    _ = _ := by norm_num
end QEC.Coding.FiberBundle.RandomBase
