-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_q4_263_absurd
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-22T06:02:23.608142+00:00
-- url     : https://prove2.me/submissions/f2691026-c028-4022-8082-084300d97136

import Mathlib

/-- False: the exponents are completely unconstrained, and `149 ∣ σ(5^36)`.
Taking `a = c = e = 0` and `b = 18` makes `sigma = ∑_{i<37} 5^i =
18189894035458564758300781 = 149 * 122079825741332649384569`. -/
theorem solution : ¬ ∀ (sigma a b c e : Nat),
    sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i) →
    149 ∣ sigma → False := by
  intro h
  refine h _ 0 18 0 0 rfl ?_
  norm_num [Finset.sum_range_succ]
