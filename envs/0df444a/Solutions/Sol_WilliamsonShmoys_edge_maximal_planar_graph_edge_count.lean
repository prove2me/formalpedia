-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:08:30.86717+00:00
-- url     : https://prove2.me/submissions/79d99e86-84c6-4f66-a951-979374320567
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_edge_maximal_graph
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound_for_edge_maximal_graph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_for_edge_maximal_graph L hV hL
  have hlower : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
    by_contra hnot
    have hlt : L.edgeSet.ncard < 3 * Fintype.card V - 6 := Nat.lt_of_not_ge hnot
    obtain ⟨M, hsub, hM, hmore⟩ :=
      WilliamsonShmoys.planar_edge_augmentation_below_bound_for_edge_maximal_graph
        L hV hL hlt
    have hmaxM := hmax M hsub hM
    omega
  omega