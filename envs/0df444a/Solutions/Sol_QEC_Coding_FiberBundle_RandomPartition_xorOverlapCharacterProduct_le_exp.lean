-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.xorOverlapCharacterProduct_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:21:34.952193+00:00
-- url     : https://prove2.me/submissions/c03d55c8-8d2f-47a3-b0d8-75ecc1aa2330

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (p : Real) (xorWeight overlap : Nat)
    (hpHalf : p ≤ 1 / 2) :
    (1 - p) ^ xorWeight * (1 - 2 * p) ^ overlap ≤
      Real.exp
        (-p * ((xorWeight : Real) + 2 * (overlap : Real))) := by
  have hbaseOne0 : 0 ≤ 1 - p := by linarith
  have hbaseTwo0 : 0 ≤ 1 - 2 * p := by linarith
  have hbaseOneExp : 1 - p ≤ Real.exp (-p) := by
    linarith [Real.add_one_le_exp (-p)]
  have hbaseTwoExp : 1 - 2 * p ≤ Real.exp (-(2 * p)) := by
    linarith [Real.add_one_le_exp (-(2 * p))]
  have hpowOne :
      (1 - p) ^ xorWeight ≤ (Real.exp (-p)) ^ xorWeight :=
    pow_le_pow_left₀ hbaseOne0 hbaseOneExp xorWeight
  have hpowTwo :
      (1 - 2 * p) ^ overlap ≤
        (Real.exp (-(2 * p))) ^ overlap :=
    pow_le_pow_left₀ hbaseTwo0 hbaseTwoExp overlap
  calc
    (1 - p) ^ xorWeight * (1 - 2 * p) ^ overlap ≤
        (Real.exp (-p)) ^ xorWeight *
          (Real.exp (-(2 * p))) ^ overlap := by
      exact mul_le_mul hpowOne hpowTwo
        (pow_nonneg hbaseTwo0 overlap)
        (pow_nonneg (Real.exp_pos (-p)).le xorWeight)
    _ = Real.exp ((xorWeight : Real) * (-p)) *
          Real.exp ((overlap : Real) * (-(2 * p))) := by
      rw [Real.exp_nat_mul, Real.exp_nat_mul]
    _ = Real.exp
          (-p * ((xorWeight : Real) + 2 * (overlap : Real))) := by
      rw [← Real.exp_add]
      congr 1
      ring
end QEC.Coding.FiberBundle.RandomPartition
