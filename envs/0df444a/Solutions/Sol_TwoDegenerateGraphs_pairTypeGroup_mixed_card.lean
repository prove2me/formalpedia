-- Prove2me | solution 1 for TwoDegenerateGraphs.pairTypeGroup_mixed_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/c5631170-dd3f-4e1b-8a93-ec25e68717e3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_sum_pairTypeGroup_card
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_false_card
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_true_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 2).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate) *
        pairParentCoordinateOneCount parents coordinate := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have htotal :
      (pairTypeGroup parents coordinate 0).card +
        (pairTypeGroup parents coordinate 1).card +
          (pairTypeGroup parents coordinate 2).card =
            parentCount.choose 2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      sum_pairTypeGroup_card parents coordinate
  rw [pairTypeGroup_false_card,
    pairTypeGroup_true_card] at htotal
  have htotal_real :
      (((parentCount -
          pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        (((pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) =
          (parentCount.choose 2 : ℝ) := by
    exact_mod_cast htotal
  rw [Nat.cast_choose_two, Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_sub hones] at htotal_real
  have hresult :
      ((pairTypeGroup parents coordinate 2).card : ℝ) =
        (((parentCount -
          pairParentCoordinateOneCount parents coordinate) *
            pairParentCoordinateOneCount parents coordinate : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hones]
    nlinarith
  exact_mod_cast hresult
end TwoDegenerateGraphs
