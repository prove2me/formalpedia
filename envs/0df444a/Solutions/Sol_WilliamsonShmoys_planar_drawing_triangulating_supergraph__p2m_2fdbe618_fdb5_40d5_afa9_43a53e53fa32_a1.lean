-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulating_supergraph__p2m_2fdbe618_fdb5_40d5_afa9_43a53e53fa32_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:29.31854+00:00
-- url     : https://prove2.me/submissions/224caa30-cf4e-4c85-b4f7-e41f072e1b59

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a7de67a5_633c_46b0_b277_259b7a4818e8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_a7de67a5_633c_46b0_b277_259b7a4818e8_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a7de67a5_633c_46b0_b277_259b7a4818e8_a1
      K hK hV
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_a7de67a5_633c_46b0_b277_259b7a4818e8_a1
      L hL hV hmax⟩