-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.exp_neg_r_div_ten_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:37:22.380198+00:00
-- url     : https://prove2.me/submissions/0ad28050-d95f-4805-8219-72cfcfcf54e6

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
    (r : Nat) (hr : 7 ≤ r) :
    Real.exp (-(r : Real) / 10) < (1 : Real) / 2 := by
  have hLog :
      Real.log 2 < (r : Real) / 10 := by
    have hSeven : (7 : Real) ≤ r := by exact_mod_cast hr
    have hApprox := Real.log_two_lt_d9
    nlinarith
  calc
    Real.exp (-(r : Real) / 10) <
        Real.exp (-Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      linarith
    _ = (1 : Real) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 2)]
      rw [one_div]
end QEC.Coding.FiberBundle.RandomPartition
