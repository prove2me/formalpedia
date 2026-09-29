-- Prove2me | solution 1 for OddPerfectNumber.split_prime_part
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:55:35.941189+00:00
-- url     : https://prove2.me/submissions/69730ca3-7cca-407e-bbb6-4478f650e094

import Mathlib

-- STAGED, NOT YET SUBMITTED (awaits publish job 254e463d).
-- Proof body extracted nearly verbatim from the accepted s=3 Dris proof
-- (Gabewhigham), whose elaboration is therefore already validated.
theorem solution (q m : Nat) (hq : q.Prime) (hm : m ≠ 0) (hqm : q ∣ m) :
    ∃ a w, 1 ≤ a ∧ m = q ^ a * w ∧ ¬ q ∣ w :=
  ⟨m.factorization q, m / q ^ (m.factorization q),
    hq.factorization_pos_of_dvd hm hqm,
    (Nat.ordProj_mul_ordCompl_eq_self m q).symm,
    Nat.not_dvd_ordCompl hq hm⟩
