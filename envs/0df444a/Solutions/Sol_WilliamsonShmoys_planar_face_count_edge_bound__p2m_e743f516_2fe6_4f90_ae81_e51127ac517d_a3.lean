-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_edge_bound__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T10:17:47.655997+00:00
-- url     : https://prove2.me/submissions/0e50e178-8054-4369-9911-33c31eff398f

import Mathlib

set_option autoImplicit false

theorem solution (v e : Nat) (lengths : List Nat)
    (hcard : Nat.le 3 v)
    (hlength : forall l : Nat, List.Mem l lengths -> Nat.le 3 l)
    (hsides : lengths.sum = 2 * e)
    (heuler : v + lengths.length = e + 2) : Nat.le (e + 6) (3 * v) := by
  have hthree : forall xs : List Nat,
      (forall x : Nat, List.Mem x xs -> 3 <= x) -> 3 * xs.length <= xs.sum := by
    intro xs
    induction xs with
    | nil =>
        intro _
        simp
    | cons a as ih =>
        intro hx
        have ha : 3 <= a := hx a List.mem_cons_self
        have htail : forall x : Nat, List.Mem x as -> 3 <= x := by
          intro x hxmem
          exact hx x (List.mem_cons_of_mem a hxmem)
        have ht : 3 * as.length <= as.sum := ih htail
        have hcons : 3 * (as.length + 1) <= a + as.sum := by omega
        rw [List.length_cons, List.sum_cons]
        exact hcons
  have hsum : 3 * lengths.length <= 2 * e := by
    have h := hthree lengths hlength
    rw [hsides] at h
    exact h
  have hfaces : lengths.length + 4 <= 2 * v := by omega
  have heq : e + 6 = v + lengths.length + 4 := by omega
  calc
    e + 6 = v + lengths.length + 4 := heq
    _ <= 3 * v := by omega