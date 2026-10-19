-- Prove2me | solution 1 for TwoDegenerateGraphs.choose_product_le_exp_binary_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/ea7fe255-5fad-441c-8589-d1929567fc44

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_choose_le_exp_binary_entropy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (population success : ι → ℕ)
    (hcount : ∀ index, success index ≤ population index) :
    (∏ index : ι,
      (population index).choose (success index) : ℝ) ≤
      Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
  calc
    (∏ index : ι,
        (population index).choose (success index) : ℝ) ≤
      ∏ index : ι,
        Real.exp
          ((population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
        apply Finset.prod_le_prod
        · intro index _
          positivity
        · intro index _
          exact choose_le_exp_binary_entropy
            (population index) (success index) (hcount index)
    _ = Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
      rw [Real.exp_sum]
end TwoDegenerateGraphs
