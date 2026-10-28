-- Prove2me | solution 1 for WilliamsonShmoys.finite_piecewise_sum_bound_small
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:05:24.841323+00:00
-- url     : https://prove2.me/submissions/af594cff-d687-44d5-aaad-93cda6f0e1da

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Fintype α] (s : Finset α) (size : α → Nat) (f : α → Nat) (n : Nat) (hPointwise : ∀ x ∈ s, f x ≤ size x) (hSum : s.sum size = n) (hn : 3 ≤ n) : s.sum f ≤ 3 * n - 6 := by
  have hsum : s.sum f ≤ s.sum size := Finset.sum_le_sum hPointwise
  omega