-- Prove2me | solution 1 for PrimePairSieve.reciprocal_weight_factor_certificate_weight
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:47:31.220684+00:00
-- url     : https://prove2.me/submissions/65bd6c91-8f15-48d4-bacc-6ff7759654bf

import Mathlib
import Definitions.Def_PrimePairSieve_ReciprocalLiteralWeight
import Definitions.Def_PrimePairSieve_reciprocal_weight_check

open scoped BigOperators
set_option autoImplicit false

theorem solution (n : ℕ) (s : Finset ℕ)
    (hcheck : PrimePairSieve.reciprocal_weight_check n s = true) :
    PrimePairSieve.reciprocal_literal_weight n =
      ∏ p ∈ s, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) := by
  have hv : (∀ p ∈ s, Nat.Prime p) ∧ (∏ p ∈ s, p) = n := of_decide_eq_true hcheck
  rcases hv with ⟨hs, hprod⟩
  have hsf : Squarefree n := by
    rw [← hprod]
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      (fun p hp => (hs p hp).squarefree)
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq
  have hfactors : n.primeFactors = s := by
    rw [← hprod]
    exact Nat.primeFactors_prod hs
  rw [PrimePairSieve.reciprocal_literal_weight, if_pos hsf, hfactors]

#print axioms solution
