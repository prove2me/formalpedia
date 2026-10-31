-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:58:28.217003+00:00
-- url     : https://prove2.me/submissions/3e20ee6f-5482-4cce-9834-2c1dd7db657c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_e780fef6_809e_4537_b9f8_0f8e159d28fc_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNDraw, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_e780fef6_809e_4537_b9f8_0f8e159d28fc_a1
      M hDraw hCard
  have hNM : N = M := hMax N hMN hNDraw
  rw [hNM] at hCount
  omega