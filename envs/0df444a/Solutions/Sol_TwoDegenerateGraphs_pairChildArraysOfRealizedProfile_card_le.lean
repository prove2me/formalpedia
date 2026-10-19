-- Prove2me | solution 1 for TwoDegenerateGraphs.pairChildArraysOfRealizedProfile_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/c3ee1ff2-7cab-4da2-8f3c-397730b5bbb6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairChildArraysOfProfile_card
import Theorems.Thm_TwoDegenerateGraphs_pairChildGroup_choose_product_entropy_bound

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hcard :
      ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) =
        ∏ index : PairBitType × Fin dimension,
          (((pairTypeGroup parents index.2 index.1).card).choose
            ((pairTypeGroupChildOnes parents children
              index.2 index.1).card) : ℝ) := by
    exact_mod_cast
      pairChildArraysOfProfile_card parents
        (pairChildCountProfile parents children)
  rw [hcard]
  exact pairChildGroup_choose_product_entropy_bound
    hparents parents children
end TwoDegenerateGraphs
