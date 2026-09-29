-- Prove2me | solution 1 for OddPerfectNumber.k_one_residue_endgame
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T11:27:03.998908+00:00
-- url     : https://prove2.me/submissions/9f0ebc04-1f57-4d04-bd8c-e77fb52f1ff7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_qr_transfer_of_one_mod_four
import Theorems.Thm_OddPerfectNumber_k_one_residue_endgame_reflected

open OddPerfectNumber

-- Reflection reduction: the proved reciprocity transfer reflects the
-- distinguished prime's residuosity back onto the Euler prime, leaving
-- the doubly-strong endgame child.
theorem solution (p m d q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime) (hqm : q ∣ m) (hqp : q ≠ p) (hqodd : Odd q)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q)
    (hsq : IsSquare (q : ZMod p)) :
    False := by
  have hq2 : q ≠ 2 := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hsqP := qr_transfer_of_one_mod_four hp hprime hp4 hq2 hqp hsq
  exact k_one_residue_endgame_reflected p m d q hp hp4 hdvd hsig
    hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP
