-- Prove2me | solution 1 for P2M_summation_by_parts__cbd93b361ef5
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:31:55.896203+00:00
-- url     : https://prove2.me/submissions/3a3a67ea-ce8b-4924-a5e4-e05eb11c7db2

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

set_option autoImplicit true

theorem solution {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  induction n with
  | zero => simp [cumsum]
  | succ n ih =>
    simp only [cumsum, Finset.sum_range_succ, Pi.mul_apply, shift, nabla] at *
    rw [ih]
    noncomm_ring
