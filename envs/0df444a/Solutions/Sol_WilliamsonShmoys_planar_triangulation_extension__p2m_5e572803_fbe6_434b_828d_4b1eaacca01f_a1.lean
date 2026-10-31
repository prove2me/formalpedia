-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_5e572803_fbe6_434b_828d_4b1eaacca01f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:24.43858+00:00
-- url     : https://prove2.me/submissions/c6d988f7-7ab7-489f-b284-e7528fba3803

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1
      L hL
  refine ⟨M, hLM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1
    M hM hV hmax