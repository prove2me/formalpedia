-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4c570e3e_7abb_4bee_95ce_463a755b298b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:41:50.152875+00:00
-- url     : https://prove2.me/submissions/a0149927-5964-4286-aee2-e054ca5dd927

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_by_edge_card__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
import Theorems.Thm_WilliamsonShmoys_le_ncard_edgeSet_eq__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  obtain ⟨H, hGH, hHdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_by_edge_card__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
      G hdraw
  refine ⟨H, hGH, hHdraw, ?_⟩
  intro K hHK hKdraw
  apply WilliamsonShmoys.le_ncard_edgeSet_eq__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2 hHK
  exact hmax K (le_trans hGH hHK) hKdraw
