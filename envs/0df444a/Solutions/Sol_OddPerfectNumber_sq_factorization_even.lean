-- Prove2me | solution 1 for OddPerfectNumber.sq_factorization_even
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:23:44.636982+00:00
-- url     : https://prove2.me/submissions/34fe65c0-3219-43eb-8194-15f387f63824

import Mathlib

-- STAGED direct proof: prime exponents in a square are even.
-- Lemma names verified against pinned Mathlib: Nat.factorization_pow
-- (Data/Nat/Factorization/Defs.lean, in namespace Nat).
theorem solution (m q : Nat) :
    Even ((m ^ 2).factorization q) := by
  have h : (m ^ 2).factorization q = 2 * m.factorization q := by
    have hf : (m ^ 2).factorization = 2 • m.factorization :=
      Nat.factorization_pow m 2
    rw [hf]
    simp [Finsupp.smul_apply, smul_eq_mul]
  exact ⟨m.factorization q, by omega⟩
