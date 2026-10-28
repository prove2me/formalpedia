-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_edge_count_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:39:35.317973+00:00
-- url     : https://prove2.me/submissions/b4f11cd0-bb68-4dfd-b7ca-41a0859208f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_component_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_component_edge_count_assembly

set_option autoImplicit false

/-- Reduction of the planar edge bound to componentwise Euler counting and finite graph bookkeeping. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  classical
  apply WilliamsonShmoys.planar_component_edge_count_assembly M hV
  intro c instS
  letI := instS
  exact WilliamsonShmoys.planarDrawingOn_component_edge_count_upper_bound M hM c