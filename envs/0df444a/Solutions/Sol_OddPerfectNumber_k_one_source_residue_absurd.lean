-- Prove2me | solution 1 for OddPerfectNumber.k_one_source_residue_absurd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:57:29.830737+00:00
-- url     : https://prove2.me/submissions/dedcb2b4-c70b-4ffe-aa5f-d6ee7f4f4a9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_sq_factorization_two
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_zmod_pow_eq_one
import Theorems.Thm_OddPerfectNumber_IsSquare_of_odd_pow_eq_one
import Theorems.Thm_OddPerfectNumber_k_one_residue_endgame

open OddPerfectNumber

-- QR reduction of the residue leaf: rewrite the local-sum range to odd
-- form, extract the residue power equation, exhibit q as a square, and
-- hand the strengthened configuration to the research-core child.
theorem solution (p m d q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime) (hqm : q ∣ m) (hqp : q ≠ p) (hqodd : Odd q)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q) :
    False := by
  have hqdvd_orig := hqdvd
  have hfact := sq_factorization_two (m := m) (q := q)
  rw [hfact] at hqdvd
  have hpow := geom_sum_dvd_implies_zmod_pow_eq_one (e := m.factorization q) hqdvd
  have hodd : Odd (2 * m.factorization q + 1) := ⟨m.factorization q, rfl⟩
  have hsq := IsSquare_of_odd_pow_eq_one (d := 2 * m.factorization q + 1) hodd hpow
  exact k_one_residue_endgame p m d q hp hp4 hdvd hsig
    hprime hqm hqp hqodd hqmem hqdvd_orig huniq hsq
