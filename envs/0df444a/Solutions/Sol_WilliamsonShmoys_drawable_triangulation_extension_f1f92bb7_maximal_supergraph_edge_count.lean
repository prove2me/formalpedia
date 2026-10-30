-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7_maximal_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:56:41.263002+00:00
-- url     : https://prove2.me/submissions/bea1a66a-bf2e-4812-bfab-8d1a288f4bb3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension_f1f92bb7_triangulation_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M)
    (hCard : 3 ≤ Fintype.card V) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hCount⟩ :=
    WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7_triangulation_completion
      M hM hCard
  have hNM : N ≤ M := hMax N hMN hN
  have hEq : M = N := le_antisymm hMN hNM
  simpa [hEq] using hCount