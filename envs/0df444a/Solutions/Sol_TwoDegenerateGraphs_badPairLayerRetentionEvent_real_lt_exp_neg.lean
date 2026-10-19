-- Prove2me | solution 1 for TwoDegenerateGraphs.badPairLayerRetentionEvent_real_lt_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/cd3a7014-a409-4168-8e7b-70cddfb22af6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_badPairLayerRetentionEvent_real_le
import Theorems.Thm_TwoDegenerateGraphs_badPairLayerRetentionBound_eq_exp

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (hbase :
      (parentCount : ℝ) +
        3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * (parentCount.choose 2 : ℝ) < -1)
    (side : Bool) :
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (midpointBeta - entropySlack)) <
      Real.exp (-(dimension : ℝ) * Real.log 2) := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (midpointBeta - entropySlack)) ≤
      ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * (midpointBeta - entropySlack))) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2)) :=
        badPairLayerRetentionEvent_real_le
          (by omega) hdimension side (midpointBeta - entropySlack)
    _ = Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) :=
        badPairLayerRetentionBound_eq_exp parentCount dimension
    _ < Real.exp (-(dimension : ℝ) * Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      have hscaled := mul_lt_mul_of_pos_left hbase
        (mul_pos hdimension_real log_two_pos)
      nlinarith
end TwoDegenerateGraphs
