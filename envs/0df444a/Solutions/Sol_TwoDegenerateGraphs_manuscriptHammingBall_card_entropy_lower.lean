-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptHammingBall_card_entropy_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/aa5e23b9-16cb-4425-be32-1764e3f2183e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_exp_binary_entropy_div_le_choose
import Theorems.Thm_TwoDegenerateGraphs_hammingBall_card_ge_boundary_binomial
import Theorems.Thm_TwoDegenerateGraphs_manuscriptHammingRadius_le_dimension

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) (word : HammingWord dimension) :
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((manuscriptHammingRadius dimension : ℝ) /
              (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      ((hammingBall dimension
        (manuscriptHammingRadius dimension) word).card : ℝ) := by
  calc
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((manuscriptHammingRadius dimension : ℝ) /
              (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      (dimension.choose (manuscriptHammingRadius dimension) : ℝ) :=
        exp_binary_entropy_div_le_choose dimension
          (manuscriptHammingRadius dimension)
          (manuscriptHammingRadius_le_dimension dimension)
    _ ≤ ((hammingBall dimension
        (manuscriptHammingRadius dimension) word).card : ℝ) := by
      exact_mod_cast hammingBall_card_ge_boundary_binomial
        dimension (manuscriptHammingRadius dimension) word
end TwoDegenerateGraphs
