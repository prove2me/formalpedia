-- Prove2me | solution 1 for TwoDegenerateGraphs.pairTypeCountProfile_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/81796dc1-a532-412a-a6f3-32ff59f0ab64

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (parentCount dimension : ℕ) :
    Fintype.card (PairTypeCountProfile parentCount dimension) =
      (parentCount.choose 2 + 1) ^ (3 * dimension) := by
  simp [PairTypeCountProfile, pow_mul, Nat.mul_comm]
end TwoDegenerateGraphs
