-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:03:04.62913+00:00
-- url     : https://prove2.me/submissions/ce17efd8-6407-4bea-8e76-fc5a184539bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_exact_edge_count__p2m_eb21a977_2509_4ef4_8e83_e4c522788ebf_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNDraw, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_completion_exact_edge_count__p2m_eb21a977_2509_4ef4_8e83_e4c522788ebf_a1
      M hCard hDraw
  have hNM : N ≤ M := hMax N hMN hNDraw
  have hEq : M = N := le_antisymm hMN hNM
  rw [hEq]
  exact hCount