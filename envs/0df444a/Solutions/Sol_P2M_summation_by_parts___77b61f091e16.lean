-- Prove2me | solution 1 for P2M_summation_by_parts___77b61f091e16
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:31:59.739814+00:00
-- url     : https://prove2.me/submissions/53fe393f-dcaf-4751-9482-e53850ddefc0

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

open BigOperators

theorem solution {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  funext n
  induction n with
  | zero => simp [shift, cumsum]
  | succ n ih =>
    simp only [shift, cumsum, nabla, Pi.mul_apply, Pi.sub_apply,
      Finset.sum_range_succ] at ih ⊢
    rw [ih]
    noncomm_ring
