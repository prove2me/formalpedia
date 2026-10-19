-- Prove2me | solution 1 for TwoDegenerateGraphs.pairLayerPair_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/874ad9e3-602a-4976-868d-0fac112e4117

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount : ℕ}
    (hparents : 2 ≤ parentCount) :
    Nonempty (PairLayer parentCount 1) := by
  apply Fintype.card_pos_iff.mp
  rw [pairLayer_card_succ parentCount 0,
    pairLayer_card_zero]
  exact Nat.choose_pos hparents
end TwoDegenerateGraphs
