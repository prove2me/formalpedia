-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_topological_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:23:21.986992+00:00
-- url     : https://prove2.me/submissions/8a2c3fb0-ef47-4539-bac2-de93b09452ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_count_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : forall W : SimpleGraph V,
      LE.le U W -> WilliamsonShmoys.HasPlanarDrawingOn W -> W = U)
    (hV : 3 <= Fintype.card V) :
    U.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨W, hUW, hW, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_completion_edge_count_v2 U hU hV
  have hWU : W = U := hmax W hUW hW
  rw [hWU] at hcount
  exact hcount
