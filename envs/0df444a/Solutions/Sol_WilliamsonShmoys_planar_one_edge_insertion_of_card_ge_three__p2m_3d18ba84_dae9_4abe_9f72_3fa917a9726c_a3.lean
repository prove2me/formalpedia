-- Prove2me | solution 1 for WilliamsonShmoys.planar_one_edge_insertion_of_card_ge_three__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:23.571504+00:00
-- url     : https://prove2.me/submissions/d3eabeb7-e862-471a-b269-c2a79f6a407c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_connect_components_by_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_extend_from_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V)
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hG_not_connected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧
      G.edgeSet.ncard < K.edgeSet.ncard := by
  rcases hG with ⟨p, arc, hp, hEdge, hCross⟩
  obtain ⟨u, v, huv, hnot, γ, hγ_cont, hγ_inj, hγ_start, hγ_end,
    hγ_vertices, hγ_edges⟩ :=
    WilliamsonShmoys.planarDrawingOn_connect_components_by_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1
      hV G p arc hp hEdge hCross hG_not_connected
  exact WilliamsonShmoys.planarDrawingOn_extend_from_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1
    G p arc hp hEdge hCross u v huv hnot γ hγ_cont hγ_inj hγ_start hγ_end
    hγ_vertices hγ_edges