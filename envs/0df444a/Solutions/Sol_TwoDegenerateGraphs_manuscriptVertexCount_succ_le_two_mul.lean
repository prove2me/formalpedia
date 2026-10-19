-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptVertexCount_succ_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/70577de7-7dcb-4b93-9b60-3bbd7d28b9a6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionProbability_mul_wordCount_eq_exp

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    manuscriptVertexCount (dimension + 1) ≤
      2 * manuscriptVertexCount dimension := by
  have hfactor :
      Real.exp ((1 - midpointBeta) * Real.log 2) ≤ (2 : ℝ) := by
    calc
      Real.exp ((1 - midpointBeta) * Real.log 2) ≤
          Real.exp (Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_pos midpointBeta_pos log_two_pos]
      _ = 2 := Real.exp_log (by norm_num)
  have hrecurrence :
      hammingRetentionProbability (dimension + 1) *
          ((2 ^ (dimension + 1) : ℕ) : ℝ) =
        Real.exp ((1 - midpointBeta) * Real.log 2) *
          (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)) := by
    rw [hammingRetentionProbability_mul_wordCount_eq_exp,
      hammingRetentionProbability_mul_wordCount_eq_exp,
      ← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold manuscriptVertexCount
  apply Nat.ceil_le.mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    3 * hammingRetentionProbability (dimension + 1) *
        ((2 ^ (dimension + 1) : ℕ) : ℝ) =
      Real.exp ((1 - midpointBeta) * Real.log 2) *
        (3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        rw [show
          3 * hammingRetentionProbability (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ) =
            3 * (hammingRetentionProbability (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ)) by ring,
          hrecurrence]
        ring
    _ ≤ 2 * (3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hfactor (by
          positivity [hammingRetentionProbability_pos dimension])
    _ ≤ 2 *
          (⌈3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) := by
        gcongr
        exact Nat.le_ceil _
end TwoDegenerateGraphs
