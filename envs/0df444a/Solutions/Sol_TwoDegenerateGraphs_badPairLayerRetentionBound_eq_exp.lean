-- Prove2me | solution 1 for TwoDegenerateGraphs.badPairLayerRetentionBound_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/2cdc7553-ca17-4bb8-885f-3a8c1e80a68d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (parentCount dimension : ℕ) :
    ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * (midpointBeta - entropySlack))) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)) =
      Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) := by
  have hparent :
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
        Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
    calc
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
          (2 : ℝ) ^ (dimension * parentCount) := by
            norm_cast
      _ = Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hprofile :
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
        Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
    calc
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
          (((parentCount.choose 2 + 1 : ℕ) : ℝ)) ^
            (3 * dimension) := by
              norm_cast
      _ = Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
              rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hretention :
      hammingRetentionProbability dimension ^
          (parentCount.choose 2) =
        Real.exp
          ((parentCount.choose 2 : ℝ) *
            (-(midpointBeta * (dimension : ℝ) * Real.log 2))) := by
    unfold hammingRetentionProbability
    rw [Real.exp_nat_mul]
  rw [hparent, hprofile, hretention,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  unfold logTwo
  push_cast
  field_simp [log_two_pos.ne']
  ring
end TwoDegenerateGraphs
