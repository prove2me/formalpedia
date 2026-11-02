-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:30:29.474338+00:00
-- url     : https://prove2.me/submissions/f077d2c6-9559-4559-a5c7-a4fb20154741

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_maximal_adjacency_count__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
import Theorems.Thm_WilliamsonShmoys_simpleGraph_eq_of_le_of_adjPairCard_le__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, ∃ dH : DecidableRel H.Adj,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H ∧
      ∀ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K = H := by
  classical
  obtain ⟨H, hHdraw, hGH, hmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_with_maximal_adjacency_count__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3 G hG
  refine ⟨H, inferInstance, hHdraw, hGH, ?_⟩
  intro K hK hHK
  exact WilliamsonShmoys.simpleGraph_eq_of_le_of_adjPairCard_le__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
    H K hHK (hmax K hK hHK)