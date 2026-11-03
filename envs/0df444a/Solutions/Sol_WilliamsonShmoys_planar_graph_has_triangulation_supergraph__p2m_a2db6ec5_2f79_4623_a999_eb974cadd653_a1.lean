-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulation_supergraph__p2m_a2db6ec5_2f79_4623_a999_eb974cadd653_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:13:07.45241+00:00
-- url     : https://prove2.me/submissions/05426ee5-a8a2-4ec5-a358-a9c60722ba27

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧ G ≤ L ∧
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj
         3 * Fintype.card V = L.edgeFinset.card + 6) := by
  obtain ⟨L, hGL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3 G hdraw hcard
  refine ⟨L, hL, hGL, ?_⟩
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  exact (hcount (hRdec := Classical.decRel L.Adj)).symm

