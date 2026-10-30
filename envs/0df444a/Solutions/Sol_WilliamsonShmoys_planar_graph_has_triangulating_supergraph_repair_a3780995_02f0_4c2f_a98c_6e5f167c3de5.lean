-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulating_supergraph_repair_a3780995_02f0_4c2f_a98c_6e5f167c3de5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:39:12.385044+00:00
-- url     : https://prove2.me/submissions/f02fca5a-e582-4ee4-8130-4256bc3803d8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count_repair_a3780995_02f0_4c2f_a98c_6e5f167c3de5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        P.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨P, hGP, hPdraw, hmax⟩ :=
    WilliamsonShmoys.planar_graph_has_maximal_drawable_supergraph G hGdraw hCard
  have hcount := WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_repair_a3780995_02f0_4c2f_a98c_6e5f167c3de5
    P hPdraw hCard hmax
  exact ⟨P, hGP, hPdraw, hcount⟩