-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_719d44f8_6785_426b_9f1b_0bb1d58add17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:31:10.437794+00:00
-- url     : https://prove2.me/submissions/5810be3b-74af-4ad9-a28c-361036ec538e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ P) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hQdraw, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion P hV hP
  have hQP : Q ≤ P := hmax Q hPQ hQdraw
  have hEq : Q = P := le_antisymm hQP hPQ
  rw [← hEq]
  exact hcount.le