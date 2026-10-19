-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingWordEdge_sum_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/055089f6-2ee5-49b0-9dc9-22864daaae6c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingWordNeighbor_sum_const

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius then weight else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  simp_rw [hammingWordNeighbor_sum_const]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring
end TwoDegenerateGraphs
