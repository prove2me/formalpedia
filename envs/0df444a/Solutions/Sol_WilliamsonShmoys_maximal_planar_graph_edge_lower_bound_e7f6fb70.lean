-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_e7f6fb70
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:43:12.461016+00:00
-- url     : https://prove2.me/submissions/94807bee-6d38-4cfa-b11e-4c11e83ec76a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_same_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) :
    3 * Fintype.card V ≤ Z.edgeSet.ncard + 6 := by
  obtain ⟨W, hZW, hWplanar, hWcount⟩ :=
    WilliamsonShmoys.planar_completion_same_vertices Z hV hZ
  have hWZ : W ≤ Z := hmax W hZW hWplanar
  have hEq : W = Z := le_antisymm hWZ hZW
  rw [hEq] at hWcount
  exact hWcount.le