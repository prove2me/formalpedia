-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_3aaeb753_8214_46cb_ae23_34cf4eb39be4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:49:25.731663+00:00
-- url     : https://prove2.me/submissions/adca3244-bf71-4d54-8635-96431641041d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_planar_supergraph__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel H.Adj := dH;
          H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨H, dH, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
      K hK
  refine ⟨H, dH, hKH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
    H dH hH hn hmax