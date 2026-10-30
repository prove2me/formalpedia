-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulation_extension_for_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:49:45.118713+00:00
-- url     : https://prove2.me/submissions/1865bdb4-883c-408f-a878-60c5ffcd8ccc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_for_edge_bound_target
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_target

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hLH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_for_edge_bound_target L hL
  exact ⟨H, hLH, hH,
    WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_target H hV hH hmax⟩