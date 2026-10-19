-- Prove2me | solution 1 for TwoDegenerateGraphs.pairChildGroup_choose_product_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/c273e497-9231-49c7-a640-21883c38d94d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_choose_product_le_exp_binary_entropy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateConditionalEntropy_log_mass

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∏ index : PairBitType × Fin dimension,
      ((pairTypeGroup parents index.2 index.1).card).choose
        ((pairTypeGroupChildOnes parents children index.2 index.1).card) : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hproduct := choose_product_le_exp_binary_entropy
    (ι := PairBitType × Fin dimension)
    (fun index => (pairTypeGroup parents index.2 index.1).card)
    (fun index =>
      (pairTypeGroupChildOnes parents children index.2 index.1).card)
    (fun index => pairTypeGroupChildOnes_card_le
      parents children index.2 index.1)
  have hsum :
      (∑ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                index.2 index.1).card : ℝ) /
              ((pairTypeGroup parents index.2 index.1).card : ℝ))) =
        (parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [pairCoordinateConditionalEntropy_log_mass
      hparents parents children]
    rw [Finset.mul_sum]
  rw [hsum] at hproduct
  exact hproduct
end TwoDegenerateGraphs
