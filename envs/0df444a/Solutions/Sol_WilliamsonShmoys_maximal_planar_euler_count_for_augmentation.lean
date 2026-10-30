-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_count_for_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:22:31.435987+00:00
-- url     : https://prove2.me/submissions/a6a6a34c-486c-4adf-8f46-9bce8f870207

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_euler_edge_count_0c08120b_590f_482f_88d1_cccf74679dd8
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hMH, hH, hEdgeLE, hCount⟩ :=
    WilliamsonShmoys.drawable_supergraph_with_euler_edge_count_0c08120b_590f_482f_88d1_cccf74679dd8 M hM hCard
  have hHM : H = M := hMax H hMH hH
  simpa [hHM] using hCount