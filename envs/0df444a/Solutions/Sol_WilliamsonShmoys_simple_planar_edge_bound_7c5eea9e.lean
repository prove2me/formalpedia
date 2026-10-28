-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound_7c5eea9e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:16:19.019501+00:00
-- url     : https://prove2.me/submissions/59d22110-131e-47cb-a4d1-a49bbc49da94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_maximal_completion_7121c0f2
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_maximal_case_7121c0f2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hKH, hcount, hHdraw, hmax⟩ :=
    WilliamsonShmoys.simple_planar_edge_bound_maximal_completion_7121c0f2 K hdraw hV
  have hbound :=
    WilliamsonShmoys.simple_planar_edge_bound_maximal_case_7121c0f2 H hHdraw hmax hV
  omega
