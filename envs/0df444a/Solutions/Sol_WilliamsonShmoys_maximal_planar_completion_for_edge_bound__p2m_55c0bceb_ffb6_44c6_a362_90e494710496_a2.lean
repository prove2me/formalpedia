-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:50:43.778335+00:00
-- url     : https://prove2.me/submissions/1640f0db-6823-4b76-9972-212a703860e5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
import Theorems.Thm_WilliamsonShmoys_finite_simple_graph_type__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
import Theorems.Thm_WilliamsonShmoys_edge_card_mono__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       H.edgeFinset.card ≤ M.edgeFinset.card) := by
  classical
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simple_graph_type__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  obtain ⟨M, hHM, hM, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_extension__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
      (fun G : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn G) H hH
  refine ⟨M, hHM, hM, ?_, ?_⟩
  · intro N hMN hN
    exact hmax N hMN hN
  · exact WilliamsonShmoys.edge_card_mono__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2 H M hHM