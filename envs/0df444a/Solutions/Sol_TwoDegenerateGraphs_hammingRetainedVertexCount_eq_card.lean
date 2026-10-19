-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedVertexCount_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/fd5a26d6-9d18-4bbe-8481-315dcf46c95e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained =
      (Fintype.card retained : ℝ) := by
  classical
  simp [hammingRetainedVertexCount, Fintype.card_subtype]
end TwoDegenerateGraphs
