-- Prove2me | solution 1 for OddPerfectNumber.k_one_source_absurd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:14:59.970106+00:00
-- url     : https://prove2.me/submissions/981ce1f9-d1ec-4761-becb-4ba8aabd87c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_source_prime_basic
import Theorems.Thm_OddPerfectNumber_k_one_source_residue_absurd

open OddPerfectNumber

-- First-level reduction of the k = 1 research residual: package the
-- elementary prime-support facts once, then isolate the order-theoretic
-- core. Staged; submit only after both children are PUBLISHED.
theorem solution (p m d q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (hm2 : 2 ≤ m)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q) :
    False := by
  obtain ⟨hprime, hqm, hqp, hqodd⟩ :=
    k_one_source_prime_basic p m q hpm hm_odd hqmem
  exact k_one_source_residue_absurd p m d q hp hp4 hdvd hsig
    hprime hqm hqp hqodd hqmem hqdvd huniq
