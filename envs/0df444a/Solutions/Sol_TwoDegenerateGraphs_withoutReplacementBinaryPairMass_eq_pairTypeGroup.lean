-- Prove2me | solution 1 for TwoDegenerateGraphs.withoutReplacementBinaryPairMass_eq_pairTypeGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/3d796581-6008-48e5-a6bc-d7ef55fa026a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_false_card
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_true_card
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_mixed_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    withoutReplacementBinaryPairMass parentCount
        (pairParentCoordinateOneCount parents coordinate) left right =
      ((pairTypeGroup parents coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
          (if left = right then (1 : ℝ) else 1 / 2) := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have hparent : 0 < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  cases left <;> cases right <;>
    simp [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount,
      pairBitTypeOfOutcomes,
      pairTypeGroup_false_card,
      pairTypeGroup_true_card,
      pairTypeGroup_mixed_card,
      Nat.cast_choose_two,
      Nat.cast_sub hones] <;>
    field_simp [hparent.ne', hparent_minus.ne']
end TwoDegenerateGraphs
