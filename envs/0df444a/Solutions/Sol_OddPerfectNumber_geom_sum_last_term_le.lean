-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_last_term_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:44:58.738917+00:00
-- url     : https://prove2.me/submissions/0eb09434-d1e9-49f7-a4ea-717084835b71

import Mathlib

theorem solution (q e : Nat) :
    q ^ e ≤ ∑ i ∈ Finset.range (e + 1), q ^ i := by
  induction e with
  | zero => simp
  | succ e ih =>
      simp only [Nat.succ_eq_add_one, Finset.sum_range_succ]
      omega
