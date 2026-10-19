-- Prove2me | solution 1 for TwoDegenerateGraphs.pairParentCoordinateSupport_card_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/e34216cd-3077-43ec-b49b-1680d39e67e9

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card +
      (pairParentCoordinateSupport parents coordinate true).card =
        parentCount := by
  classical
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin parentCount)))
      (fun parent => parents parent coordinate = false)
  simpa [pairParentCoordinateSupport, Bool.not_eq_false] using hpartition
end TwoDegenerateGraphs
