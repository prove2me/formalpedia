-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_edge_bound__p2m_ab59570c_fffd_4137_a2d3_71557bc91725_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:23:01.361332+00:00
-- url     : https://prove2.me/submissions/20b5c264-6991-4cb8-8323-3ac4259b5e97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1 G hG
  refine ⟨H, hGH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_bound__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
    H hCard hH hMax