-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingParentTuple_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/c4ef4cf5-96ee-430d-9b0a-7297ad8fe6f7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (parentCount dimension : ℕ) :
    Fintype.card (Fin parentCount → HammingWord dimension) =
      2 ^ (dimension * parentCount) := by
  simp [HammingWord, ← pow_mul]
end TwoDegenerateGraphs
