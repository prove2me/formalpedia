-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fddd844c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:42:58.388336+00:00
-- url     : https://prove2.me/submissions/3189e300-3009-4b30-bc06-13653632f5d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_edge_maximal_supergraph_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
import Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_graph_card_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      M.edgeSet ⊆ N.edgeSet → N.edgeSet = M.edgeSet) :
    3 * (Fintype.card V : Int) - 6 ≤ (M.edgeSet.ncard : Int) := by
  obtain ⟨N, hN, hSub, hNMax⟩ :=
    WilliamsonShmoys.drawable_graph_has_edge_maximal_supergraph_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734 M hM
  have hSet : N.edgeSet = M.edgeSet := hMax N hN hSub
  have hCount :=
    WilliamsonShmoys.edge_maximal_drawable_graph_card_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
      N hN hCard hNMax
  rw [hSet] at hCount
  omega