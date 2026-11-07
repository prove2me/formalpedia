-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.real_pow_eq_exp_nat_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:25:44.157187+00:00
-- url     : https://prove2.me/submissions/d8a41e7c-e990-4591-95da-6072a4c43a67

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
    (x : Real) (n : Nat) (hx : 0 < x) :
    x ^ n = Real.exp ((n : Real) * Real.log x) := by
  calc
    x ^ n = (Real.exp (Real.log x)) ^ n := by
      rw [Real.exp_log hx]
    _ = Real.exp ((n : Real) * Real.log x) := by
      rw [Real.exp_nat_mul]
end QEC.Coding.FiberBundle.RandomPartition
