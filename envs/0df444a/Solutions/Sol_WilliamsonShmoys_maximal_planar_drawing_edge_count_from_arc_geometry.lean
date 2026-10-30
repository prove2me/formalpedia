-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_from_arc_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:34:18.699533+00:00
-- url     : https://prove2.me/submissions/f5120686-d3ec-4ab2-8de2-b2747ae0b957

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_to_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_to_triangulation M hV hM
  have hNM : N = M := hmax N hMN hN
  rw [← hNM]
  exact hcount