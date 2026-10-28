-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:40:57.601659+00:00
-- url     : https://prove2.me/submissions/3f3537b6-034d-4e2a-80c7-ea148ac52e0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion_with_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : forall Y : SimpleGraph V,
      LE.le X Y -> WilliamsonShmoys.HasPlanarDrawingOn Y -> Y = X)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= X.edgeSet.ncard := by
  obtain ⟨Y, hXY, hY, hcount⟩ :=
    WilliamsonShmoys.exists_maximal_planar_completion_with_edge_count X hX hV
  have hYX : Y = X := hmax Y hXY hY
  subst Y
  omega