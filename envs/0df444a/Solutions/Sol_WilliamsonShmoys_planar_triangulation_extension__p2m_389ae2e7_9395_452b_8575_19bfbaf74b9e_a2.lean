-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_389ae2e7_9395_452b_8575_19bfbaf74b9e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:56:09.021693+00:00
-- url     : https://prove2.me/submissions/945be49a-09d8-49d8-91f6-8ed73228297b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1
      K hK
  have hcount :=
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1
      L hL hCard hmax
  exact ⟨L, hKL, hL, hcount⟩