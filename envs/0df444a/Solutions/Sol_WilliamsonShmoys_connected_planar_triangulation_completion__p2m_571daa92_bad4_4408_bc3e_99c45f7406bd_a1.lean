-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_triangulation_completion__p2m_571daa92_bad4_4408_bc3e_99c45f7406bd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:42.640295+00:00
-- url     : https://prove2.me/submissions/8933f97e-e0f9-4384-b288-db86694f0662

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_completion__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1

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
       WilliamsonShmoys.HasPlanarDrawingOn H ∧
       G.edgeFinset.card ≤ H.edgeSet.ncard ∧
       H.edgeSet.ncard = 3 * Fintype.card V - 6) := by
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨H, hGH, hconn, hplanar, hcount, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_completion__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
      G hG hcard
  letI : DecidableRel H.Adj := Classical.decRel _
  have hformula :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
      H hconn hplanar hcard hmax
  exact ⟨H, hGH, hconn, hplanar, hcount, hformula⟩
