-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_bound__p2m_c26a86c1_c11b_4f85_a158_b9e12bec4015_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:10.257483+00:00
-- url     : https://prove2.me/submissions/30b37b00-268b-48a8-8fca-01031baf2c4a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_edge_maximal__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (hdec : DecidableRel H.Adj),
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeFinset.card ≤ H.edgeFinset.card ∧
      H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hdec, hsub, hdraw, hle, hmax⟩ := WilliamsonShmoys.planar_extension_edge_maximal__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1 G hG
  exact ⟨H, hdec, hsub, hdraw, hle, WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1 H hdraw hmax hcard⟩
