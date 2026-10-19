-- Prove2me | solution 1 for TwoDegenerateGraphs.pairParentCoordinateSupport_true_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/b2c3da1f-e822-4a4a-9211-b00acc85424e

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
    (pairParentCoordinateSupport parents coordinate true).card =
      pairParentCoordinateOneCount parents coordinate := by
  rfl
end TwoDegenerateGraphs
