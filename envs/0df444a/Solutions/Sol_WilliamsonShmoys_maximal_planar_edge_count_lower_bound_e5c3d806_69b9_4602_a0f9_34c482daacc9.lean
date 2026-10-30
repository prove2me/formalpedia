-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:04:00.861602+00:00
-- url     : https://prove2.me/submissions/3182cbde-dc5f-40f8-a3b2-bd71f2e2abe7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_with_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ W : SimpleGraph V,
      LE.le Z W →
      WilliamsonShmoys.HasPlanarDrawingOn W →
      W = Z)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ Z.edgeSet.ncard := by
  obtain ⟨W, hZW, hW, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_with_triangulation Z hZ hV
  have hWZ : W = Z := hmax W hZW hW
  rw [hWZ] at hcount
  omega