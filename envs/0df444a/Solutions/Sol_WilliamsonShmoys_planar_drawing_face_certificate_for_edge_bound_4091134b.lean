-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_certificate_for_edge_bound_4091134b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:23:00.97943+00:00
-- url     : https://prove2.me/submissions/9381bba8-5e16-46d9-beca-37d1344d4b87

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_certificate_for_edge_bound_4091134b

open WilliamsonShmoys

set_option autoImplicit false

private theorem list_three_mul_length_le_sum (xs : List Nat)
    (h : forall k, k ∈ xs -> 3 <= k) :
    3 * xs.length <= xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : 3 <= a := h a (by simp)
      have htail : forall k, k ∈ xs -> 3 <= k := by
        intro k hk
        exact h k (by simp [hk])
      have hxs := ih htail
      simp only [List.length_cons, List.sum_cons]
      nlinarith

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hconn : T.Connected)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = T.edgeSet.ncard + 2 /\
      3 * f <= 2 * T.edgeSet.ncard := by
  obtain ⟨lengths, hmin, hsum, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_face_boundary_certificate_for_edge_bound_4091134b
      T hdraw hconn hV
  have hbound : 3 * lengths.length <= lengths.sum :=
    list_three_mul_length_le_sum lengths hmin
  refine ⟨lengths.length, heuler, ?_⟩
  calc
    3 * lengths.length <= lengths.sum := hbound
    _ = 2 * T.edgeSet.ncard := hsum