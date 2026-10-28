-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_for_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:32:42.369641+00:00
-- url     : https://prove2.me/submissions/5d3a5a36-050a-4058-9643-08a65b4a5460
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_inclusion_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_exact_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hWdraw : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ T : SimpleGraph V,
      W ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hWT, hTdraw, hTmax⟩ :=
    WilliamsonShmoys.finite_inclusion_maximal_extension W hWdraw
  exact ⟨T, hWT, hTdraw,
    WilliamsonShmoys.maximal_drawing_exact_edge_count T hCard hTdraw hTmax⟩