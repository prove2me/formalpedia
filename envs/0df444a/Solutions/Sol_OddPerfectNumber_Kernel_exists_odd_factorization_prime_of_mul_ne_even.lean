-- Prove2me | solution 1 for OddPerfectNumber.Kernel.exists_odd_factorization_prime_of_mul_ne_even
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T08:18:25.489562+00:00
-- url     : https://prove2.me/submissions/2762a352-9fa7-426f-ac35-a73cc566e0f7

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.exists_odd_factorization_prime_of_mul_ne_even
--          259d71b5-76cb-4936-a7e1-ecec332a8ca3
--
-- An odd multiplicity in a product forces an odd multiplicity in one factor.
--
-- This is the reusable step behind
-- `index_prime_has_odd_multiplicity_source` (48e8fb88).  Once the sigma
-- product decomposition (39086529) is available, the second Dris equation
-- `sigma(m^2) = p^5 * s` with `p ∤ s` gives `v_p(sigma(m^2)) = 5`, and the
-- product identity says that valuation is the sum of the valuations of the
-- individual local factors `sigma(t^(2 e_t))`.  A sum of five odd-or-even
-- integers can only be odd if one of them is odd, and this child is the formal
-- content of that observation: it is the two-factor case, applied repeatedly.
--
-- Diagnostic notes.  The proof is a by-contra: if both factors had even
-- multiplicity at p, their sum would be even, hence so would the product.
-- `Nat.factorization_mul` is the accepted decomposition of a product, taken
-- from `20_UniqueOddMultNonSquare.lean:12` in the same directory, which uses
-- it as `Nat.factorization_mul (Nat.prime_ne_one hq) (Nat.prime_ne_one hr)`.
-- Only the non-degeneracy side conditions are needed here, so they are
-- discharged directly from `ha0`/`hb0` rather than from primality.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace ParitySplit

theorem solution_aux {a b p : Nat}
    (ha : a != 0) (hb : b != 0) (hp : p.Prime)
    (hodd : Not (Even ((a * b).factorization p))) :
    Not (Even (a.factorization p)) \/ Not (Even (b.factorization p)) := by
  have ha0 : a ≠ 0 := by simpa using ha
  have hb0 : b ≠ 0 := by simpa using hb
  by_contra hcon
  push_neg at hcon
  have hea : Even (a.factorization p) := hcon.1
  have heb : Even (b.factorization p) := hcon.2
  have hmul :
      (a * b).factorization = a.factorization + b.factorization :=
    Nat.factorization_mul ha0 hb0
  have h : (a * b).factorization p = a.factorization p + b.factorization p := by
    rw [hmul]
    rfl
  obtain ⟨ka, hka⟩ := hea
  obtain ⟨kb, hkb⟩ := heb
  refine hodd ?_
  have hsum : Even (a.factorization p + b.factorization p) := ⟨ka + kb, by
    rw [hka, hkb]
    omega⟩
  rwa [← h] at hsum

end ParitySplit
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {a b p : Nat}
    (ha : a != 0) (hb : b != 0) (hp : p.Prime)
    (hodd : Not (Even ((a * b).factorization p))) :
    Not (Even (a.factorization p)) \/ Not (Even (b.factorization p)) :=
  OddPerfectNumber.Kernel.ParitySplit.solution_aux ha hb hp hodd
