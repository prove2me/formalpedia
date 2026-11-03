-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_supergraph_edge_bounds__p2m_9fc83de8_0852_4661_9f7b_4eaba74d4214_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:53:55.413323+00:00
-- url     : https://prove2.me/submissions/98673474-2bc6-446e-bb12-5ee184085824

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_completion__p2m_571daa92_bad4_4408_bc3e_99c45f7406bd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    ∃ H : SimpleGraph V,
      (letI : DecidableRel H.Adj := Classical.decRel _;
       G ≤ H ∧ H.Connected ∧
       G.edgeFinset.card ≤ H.edgeSet.ncard ∧
       Fintype.card V ≤ H.edgeSet.ncard + 2 ∧
       H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨H, hsub, hconn, _hplanar, hGcard, hEq⟩ :=
    WilliamsonShmoys.connected_planar_triangulation_completion__p2m_571daa92_bad4_4408_bc3e_99c45f7406bd_a1
      G hG hcard
  letI : DecidableRel H.Adj := Classical.decRel _
  refine ⟨H, hsub, hconn, hGcard, ?_, ?_⟩
  · omega
  · omega