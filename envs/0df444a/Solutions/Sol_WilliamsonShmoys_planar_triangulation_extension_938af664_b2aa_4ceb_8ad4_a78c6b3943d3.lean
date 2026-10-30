-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:36:42.841826+00:00
-- url     : https://prove2.me/submissions/5c9ce409-540f-4088-91d8-e48d7cbde8e0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension_391f3239_9f51_4455_9b2f_cbbc61103aca
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_graph_edge_count_391f3239_9f51_4455_9b2f_cbbc61103aca

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hGM, hMdraw, hMmax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_maximal_extension_391f3239_9f51_4455_9b2f_cbbc61103aca
      G hV hG
  exact ⟨M, hGM, hMdraw,
    WilliamsonShmoys.planar_edge_maximal_graph_edge_count_391f3239_9f51_4455_9b2f_cbbc61103aca
      M hV hMdraw hMmax⟩