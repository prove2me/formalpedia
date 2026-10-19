-- Prove2me | solution 1 for TwoDegenerateGraphs.pairTypeGroup_true_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/931b7155-c0fc-49b9-9aff-d8ed8868f058

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairParentCoordinateSupport_true_card
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
    (pairTypeGroup parents coordinate 1).card =
      (pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_true_card] using
    pairTypeGroup_homogeneous_card parents coordinate true
end TwoDegenerateGraphs
