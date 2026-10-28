-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_6daa1fb6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:35:28.729991+00:00
-- url     : https://prove2.me/submissions/a905a6c1-a89e-4ce7-af0f-b01365cd1d1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hMax : forall Z : SimpleGraph V, HasPlanarDrawingOn Z ->
      (forall u v, Y.Adj u v -> Z.Adj u v) -> Z = Y)
    (hCard : 3 <= Fintype.card V) :
    (Y.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨Z, hZ, hYZ, hEdges⟩ :=
    WilliamsonShmoys.planar_maximal_edge_count Y hY hCard
  have hEq : Z = Y := hMax Z hZ hYZ
  rw [hEq] at hEdges
  exact hEdges