-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:40:04.086152+00:00
-- url     : https://prove2.me/submissions/41f611c1-1e01-4827-bb0e-9f50aa312eb8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_completion_maximal_extension_for_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hNH, hHdraw, hmax⟩ :=
    WilliamsonShmoys.exists_drawable_completion_maximal_extension_for_edge_count N hV hN
  exact ⟨H, hNH, hHdraw,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_count H hV hHdraw hmax⟩