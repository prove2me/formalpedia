-- Prove2me | solution 1 for WilliamsonShmoys.has_planar_drawing_on_edge_count_le_three_card_sub_six
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:41:56.223266+00:00
-- url     : https://prove2.me/submissions/7d445014-77ac-4217-9e43-336ce59b8c32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_has_planar_drawing_on_connected_supergraph_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_bound_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hEdges, hHdraw, hHconn⟩ :=
    WilliamsonShmoys.has_planar_drawing_on_connected_supergraph_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18
      G hG hCard
  calc
    G.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hEdges
    _ ≤ 3 * Fintype.card V - 6 :=
      WilliamsonShmoys.connected_planar_drawing_edge_count_bound_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18
        H hHdraw hHconn hCard