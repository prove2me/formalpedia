-- Prove2me | solution 1 for TwoDegenerateGraphs.pairTypeGroup_false_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/653b8d7a-e44a-4177-ad75-f451f0d2633d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairParentCoordinateSupport_false_card
import Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_homogeneous_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 0).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_false_card] using
    pairTypeGroup_homogeneous_card parents coordinate false
end TwoDegenerateGraphs
