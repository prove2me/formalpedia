-- Prove2me | solution 1 for TwoDegenerateGraphs.pairParentCoordinateSupport_false_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/bfde95a4-ef00-4590-80fb-394723073225

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairParentCoordinateSupport_true_card
import Theorems.Thm_TwoDegenerateGraphs_pairParentCoordinateSupport_card_add

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card =
      parentCount - pairParentCoordinateOneCount parents coordinate := by
  have hpartition := pairParentCoordinateSupport_card_add parents coordinate
  rw [pairParentCoordinateSupport_true_card] at hpartition
  omega
end TwoDegenerateGraphs
