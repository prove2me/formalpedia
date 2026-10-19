-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingWordNeighbor_sum_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/6fe37617-540d-4028-90fe-a566ffec28df

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingBall_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) (left : HammingWord dimension)
    (weight : ℝ) :
    (∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then weight else 0) =
      ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  calc
    (∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then weight else 0) =
        ∑ _right ∈ hammingBall dimension radius left, weight := by
          rw [← Finset.sum_filter]
          rfl
    _ = ((hammingBall dimension radius left).card : ℝ) * weight := by
      simp [nsmul_eq_mul]
    _ = ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) * weight := by
      rw [hammingBall_card]
end TwoDegenerateGraphs
