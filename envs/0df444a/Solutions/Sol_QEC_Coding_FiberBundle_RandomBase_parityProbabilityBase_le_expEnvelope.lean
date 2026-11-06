-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_le_expEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:29:11.395189+00:00
-- url     : https://prove2.me/submissions/dcc07e9e-94ab-4450-9832-b35994bfa6dd

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (p : Real) (w : Nat) (hpHalf : p ≤ 1 / 2) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤
      (1 + Real.exp (-2 * (p * w))) / 2 := by
  have hbase_nonneg : 0 ≤ 1 - 2 * p := by linarith
  have hbase_exp : 1 - 2 * p ≤ Real.exp (-2 * p) := by
    linarith [Real.add_one_le_exp (-2 * p)]
  have hpow :
      (1 - 2 * p) ^ w ≤ Real.exp (-2 * (p * w)) := by
    calc
      _ ≤ (Real.exp (-2 * p)) ^ w :=
        pow_le_pow_left₀ hbase_nonneg hbase_exp w
      _ = Real.exp ((w : Real) * (-2 * p)) := by
        rw [Real.exp_nat_mul]
      _ = _ := by
        congr 1
        ring
  linarith
end QEC.Coding.FiberBundle.RandomBase
