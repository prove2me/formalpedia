-- Prove2me | solution 1 for TwoDegenerateGraphs.degree_gt_two_of_three_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/2fff05b9-be71-4d1f-bedf-4cbce31793af

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v x y z : V)
    (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    2 < G.degree v := by
  classical
  change 2 < (G.neighborFinset v).card
  apply Finset.two_lt_card_iff.mpr
  exact ⟨x, y, z,
    (G.mem_neighborFinset v x).mpr hx,
    (G.mem_neighborFinset v y).mpr hy,
    (G.mem_neighborFinset v z).mpr hz,
    hxy, hxz, hyz⟩
end TwoDegenerateGraphs
