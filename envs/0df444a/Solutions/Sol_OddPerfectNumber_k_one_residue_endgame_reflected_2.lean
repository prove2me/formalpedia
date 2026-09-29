-- Prove2me | solution 2 for OddPerfectNumber.k_one_residue_endgame_reflected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T11:44:50.913492+00:00
-- url     : https://prove2.me/submissions/b60dd7b1-186d-4c96-9b50-d303c85c403e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_endgame_q_dvd_d
import Theorems.Thm_OddPerfectNumber_k_one_endgame_q_dvd_t

theorem _root_.solution (p m d q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime) (hqm : q ∣ m) (hqp : q ≠ p) (hqodd : Odd q)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q)
    (hsq : IsSquare (q : ZMod p))
    (hsqP : IsSquare (p : ZMod q)) :
    False := by
  have hqm2 : q ∣ ((p + 1) / 2) * d := by
    rw [← hdvd]
    exact dvd_pow hqm (by norm_num)
  rcases (Nat.Prime.dvd_mul hprime).1 hqm2 with hqt | hqd
  · exact OddPerfectNumber.k_one_endgame_q_dvd_t p m d q hp hp4 hdvd hsig
      hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP hqt
  · exact OddPerfectNumber.k_one_endgame_q_dvd_d p m d q hp hp4 hdvd hsig
      hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP hqd

#print axioms solution
