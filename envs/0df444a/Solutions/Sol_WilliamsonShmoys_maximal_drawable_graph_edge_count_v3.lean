-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:04:28.992564+00:00
-- url     : https://prove2.me/submissions/e9389f0d-23f3-4cf8-845a-82b016d137b0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_completion_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : ∀ Z : SimpleGraph V,
      LE.le Y Z →
      WilliamsonShmoys.HasPlanarDrawingOn Z →
      Z = Y)
    (hV : 3 ≤ Fintype.card V) :
    Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Z, hYZ, hZ, hcount⟩ :=
    WilliamsonShmoys.exists_planar_edge_count_completion_v2 Y hY hV
  have hEq : Z = Y := hmax Z hYZ hZ
  rw [hEq] at hcount
  exact hcount