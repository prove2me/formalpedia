-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_supergraph_face_count__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:49:52.518979+00:00
-- url     : https://prove2.me/submissions/3d17c13d-5d53-4874-827b-cafd1ca6400e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_edge_bounds__p2m_9fc83de8_0852_4661_9f7b_4eaba74d4214_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧
      G.edgeFinset.card ≤ H.edgeSet.ncard ∧
      ∃ f : Nat,
        Fintype.card V + f = H.edgeSet.ncard + 2 ∧
        3 * f ≤ 2 * H.edgeSet.ncard := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨H, hH⟩ :=
    WilliamsonShmoys.connected_planar_supergraph_edge_bounds__p2m_9fc83de8_0852_4661_9f7b_4eaba74d4214_a2
      G hG hcard
  letI : DecidableRel H.Adj := Classical.decRel _
  rcases hH with ⟨hGH, hconn, hGedge, hlower, hupper⟩
  let m : Nat := H.edgeSet.ncard
  let f : Nat := m + 2 - Fintype.card V
  refine ⟨H, hGH, hconn, hGedge, ⟨f, ?_, ?_⟩⟩
  · dsimp only [f, m]
    omega
  · dsimp only [f, m]
    omega