-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:56:19.189456+00:00
-- url     : https://prove2.me/submissions/d9bdaa3c-5a08-4d75-930f-0d49ccd08a26

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_maximal_extension_47cfe247_f32d_4afb_b363_54161b3a97c2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_completion_maximal_extension_47cfe247_f32d_4afb_b363_54161b3a97c2 M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2 N hV hN hmax⟩