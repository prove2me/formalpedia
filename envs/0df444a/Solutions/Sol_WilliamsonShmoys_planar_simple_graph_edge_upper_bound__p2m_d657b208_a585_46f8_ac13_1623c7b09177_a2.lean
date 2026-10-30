-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:41:10.051037+00:00
-- url     : https://prove2.me/submissions/d8ee351f-3b1f-41ad-83ea-8a9fc8fd91f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_face_count__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
import Theorems.Thm_WilliamsonShmoys_face_count_arithmetic__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨H, hGH, hConn, hSub, f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.connected_planar_supergraph_face_count__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
      G hG
  have hArithmetic :=
    WilliamsonShmoys.face_count_arithmetic__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
      (Fintype.card V) H.edgeSet.ncard f hcard hEuler hFaces
  exact le_trans hSub hArithmetic