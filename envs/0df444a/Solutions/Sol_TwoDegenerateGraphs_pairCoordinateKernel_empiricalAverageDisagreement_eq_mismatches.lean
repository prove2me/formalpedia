-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/f995d1d5-165a-4f80-bf7c-c4d2c6afc40e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateKernel_empiricalAverageDisagreement
import Theorems.Thm_TwoDegenerateGraphs_sum_pairCoordinatePairMismatchCount

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair : ℕ) : ℝ) /
        (2 * (parentCount.choose 2 : ℝ)) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hone := pairTypeGroupChildOnes_card_le
    parents children coordinate 1
  rw [pairCoordinateKernel_empiricalAverageDisagreement
    hparents parents children coordinate,
    sum_pairCoordinatePairMismatchCount]
  push_cast [hone]
  field_simp [hpair.ne']
end TwoDegenerateGraphs
