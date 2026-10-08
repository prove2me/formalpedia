-- Prove2me | solution 1 for PrimePairSieve.reciprocal_weight_factor_certificate_sound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:20:23.361984+00:00
-- url     : https://prove2.me/submissions/78abe041-663f-4bd8-8cf5-99ba2b78e5a4

import Mathlib
import Definitions.Def_PrimePairSieve_reciprocal_weight_check

open scoped BigOperators
set_option autoImplicit false

theorem solution (n : ℕ) (s : Finset ℕ)
    (hcheck : PrimePairSieve.reciprocal_weight_check n s = true) :
    Squarefree n ∧ n.primeFactors = s := by
  have hv : (∀ p ∈ s, Nat.Prime p) ∧ (∏ p ∈ s, p) = n := of_decide_eq_true hcheck
  rcases hv with ⟨hs, hprod⟩
  subst n
  have hsf : Squarefree (∏ p ∈ s, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      (fun p hp => (hs p hp).squarefree)
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq
  exact ⟨hsf, Nat.primeFactors_prod hs⟩

#print axioms solution
