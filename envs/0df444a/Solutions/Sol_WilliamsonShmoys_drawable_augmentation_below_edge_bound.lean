-- Prove2me | solution 1 for WilliamsonShmoys.drawable_augmentation_below_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:16:07.625137+00:00
-- url     : https://prove2.me/submissions/342de9a8-3ecc-47f3-82e1-86cf7b841933
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_e2343c2d
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound_e2343c2d

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn M)
    (hE : M.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N ≠ M ∧ HasPlanarDrawingOn N := by
  obtain ⟨N, hMN, hcard, hdrawN, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_e2343c2d M hdraw
  have hbound :=
    WilliamsonShmoys.maximal_drawable_edge_bound_e2343c2d N hdrawN hmax hV
  have hneq : N ≠ M := by
    intro hNM
    have hcontra : 3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
      simpa [hNM] using hbound
    omega
  exact ⟨N, hMN, hneq, hdrawN⟩