-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingHost_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/5ef95729-caec-41a6-a847-755c5d8c5659

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution (dimension radius : ℕ)
    (x y : Bool × HammingWord dimension) :
    (hammingHost dimension radius).Adj x y ↔
      x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius := by
  rw [hammingHost, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, hforward | hbackward⟩
    · exact hforward
    · exact ⟨Ne.symm hbackward.1, by
        simpa [hammingDist_comm] using hbackward.2⟩
  · intro hxy
    refine ⟨?_, Or.inl hxy⟩
    intro heq
    exact hxy.1 (congrArg Prod.fst heq)
end TwoDegenerateGraphs
