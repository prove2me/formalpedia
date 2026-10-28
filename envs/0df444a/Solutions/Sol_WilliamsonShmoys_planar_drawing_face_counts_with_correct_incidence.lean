-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_counts_with_correct_incidence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:07:00.089393+00:00
-- url     : https://prove2.me/submissions/10c3551c-2b95-456d-a5c1-c11bc9cc42b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_ac816c5dcb924d25
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_ac816c5dcb924d25

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count_ac816c5dcb924d25 H hV hconn hH
  have hedge :=
    WilliamsonShmoys.planar_drawing_edge_bound_ac816c5dcb924d25 H hV hconn hH
  refine ⟨f, heuler, ?_⟩
  omega