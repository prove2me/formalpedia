-- Prove2me | solution 1 for WilliamsonShmoys.finite_piecewise_sum_bound_large_aggregate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:05:37.198887+00:00
-- url     : https://prove2.me/submissions/e6fb2415-7f49-4ecf-a5db-f4af1b8425d3

import Mathlib

set_option autoImplicit false

open Finset

theorem solution {α : Type} [Fintype α] (s : Finset α) (a b : α → Nat) (x : α)
    (hx : x ∈ s) (hAll : ∀ y ∈ s, b y ≤ 3 * a y)
    (hMargin : b x + 6 ≤ 3 * a x) : s.sum b + 6 ≤ 3 * (s.sum a) := by
  classical
  have hpoint : s.sum (fun y => b y + if y = x then 6 else 0) ≤
      s.sum (fun y => 3 * a y) := by
    apply Finset.sum_le_sum
    intro y hy
    by_cases hyx : y = x
    · subst y
      simpa using hMargin
    · simpa [hyx] using hAll y hy
  have hbonus : s.sum (fun y => if y = x then 6 else 0) = 6 := by
    simp [hx]
  have hsum : s.sum (fun y => b y + if y = x then 6 else 0) = s.sum b + 6 := by
    rw [Finset.sum_add_distrib, hbonus]
  have hscale : s.sum (fun y => 3 * a y) = 3 * s.sum a := by
    rw [← Finset.mul_sum]
  calc
    s.sum b + 6 = s.sum (fun y => b y + if y = x then 6 else 0) := hsum.symm
    _ ≤ s.sum (fun y => 3 * a y) := hpoint
    _ = 3 * s.sum a := hscale