-- Prove2me | solution 1 for WilliamsonShmoys.drawable_add_edge_of_nonreachable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:05:08.865075+00:00
-- url     : https://prove2.me/submissions/09b6c557-0f4d-4468-8c4f-f28f0e6ba0f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) {u v : V}
    (huv : ¬ H.Reachable u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K ≠ H := by
  obtain ⟨K, hsub, hdrawK, hneq, _hedge⟩ :=
    WilliamsonShmoys.planar_edge_extension H hdraw (u := u) (v := v) huv
  exact ⟨K, hsub, hdrawK, hneq⟩