-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_count_euler_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:36:19.313986+00:00
-- url     : https://prove2.me/submissions/f6619226-4193-4c4f-b9fd-c7ad33a44e98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_face_data
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨faces, boundaryLength, hEuler, hTotal, hBoundary⟩ :=
    WilliamsonShmoys.planarDrawingOn_has_face_data Y hV hconn hY
  have hLower : 3 * faces ≤ ∑ f : Fin faces, boundaryLength f := by
    calc
      3 * faces = ∑ _f : Fin faces, 3 := by
        simpa using (Nat.mul_comm 3 faces)
      _ ≤ ∑ f : Fin faces, boundaryLength f :=
        Finset.sum_le_sum fun f _ => hBoundary f
  have hEdges : 3 * faces ≤ 2 * Y.edgeSet.ncard := by
    rw [hTotal] at hLower
    exact hLower
  omega