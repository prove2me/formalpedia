-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionProbability_sq_mul_wordCount_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/f943d215-4673-4ee2-9ce3-94324025f2ee

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - 2 * midpointBeta) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold hammingRetentionProbability
  rw [hwords, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring
end TwoDegenerateGraphs
