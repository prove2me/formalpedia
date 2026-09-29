-- Prove2me | solution 1 for OddPerfectNumber.k_one_endgame_q_dvd_d_normalization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T04:22:52.205002+00:00
-- url     : https://prove2.me/submissions/e4a09ad4-7ee4-4705-9f29-090b6c70a653
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_source_residue_absurd

open OddPerfectNumber

-- Intentional reduction: the live normalization leaf has all hypotheses of
-- the independently named unique-source research core.  This is a sketch;
-- it does not assert that the open core has been proved.
theorem solution (p m d q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime) (hqm : q ∣ m) (hqp : q ≠ p) (hqodd : Odd q)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q)
    (hsq : IsSquare (q : ZMod p))
    (hsqP : IsSquare (p : ZMod q))
    (hqd : q ∣ d) :
    Odd m ∧ ¬ p ∣ m := by
  have hfalse : False := k_one_source_residue_absurd p m d q hp hp4 hdvd hsig
    hprime hqm hqp hqodd hqmem hqdvd huniq
  exact hfalse.elim
