-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinateKernel_parentProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/5d2b3797-8596-4902-8cf6-147b9b9451da

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairCoordinateKernel hparents parents children coordinate).parentProbability =
      (pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ) := by
  rfl
end TwoDegenerateGraphs
