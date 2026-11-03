-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_sharp_edge_count__p2m_804de7f6_f862_47b4_add3_5edea203f43e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:20:55.111888+00:00
-- url     : https://prove2.me/submissions/e923dd07-1710-49b2-bf9c-14ace84066dc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
      K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
      L hL hcard hMax⟩