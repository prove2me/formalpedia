-- Prove2me | solution 1 for OddPerfectNumber.q_dvd_of_factorization_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T17:51:31.668929+00:00
-- url     : https://prove2.me/submissions/a81c1ba4-d9d9-460b-a998-33f3c2f8edda

import Mathlib

theorem solution (q t d m A r : Nat)
    (hq : q.Prime) (hm2 : m ^ 2 ≠ 0) (ht0 : t ≠ 0) (hd0 : d ≠ 0)
    (hdvd : m ^ 2 = t * d)
    (hA : (m ^ 2).factorization q = A)
    (hr : t.factorization q = r)
    (hstrict : r < A) :
    q ∣ d := by
  by_contra hnot
  have hdfac : d.factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot
  have hfac : (m ^ 2).factorization
      = t.factorization + d.factorization := by
    rw [hdvd]
    exact Nat.factorization_mul ht0 hd0
  have hpoint := congrArg (fun f : ℕ →₀ ℕ => f q) hfac
  simp only [Finsupp.add_apply] at hpoint
  rw [hA, hr, hdfac] at hpoint
  omega
