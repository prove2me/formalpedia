-- Prove2me | solution 1 for OddPerfectNumber.Kernel.two_prime_block_is_prime_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T16:20:59.894996+00:00
-- url     : https://prove2.me/submissions/8bc7386f-af26-4c0b-b5ed-aee4715c43a2

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.two_prime_block_is_prime_mul_sq
--          672c3afb-a666-41e5-b792-996d5d5db518
--
-- Pure composition.  The counting child
-- `two_prime_odd_mult_unique_of_both_non_square` (4308037b) turns the square
-- relation `y ^ 2 = q * r * a * b` with coprime non-square blocks into a unique
-- odd-multiplicity prime `t` of `a`; the accepted reconstruction child
-- `odd_mult_single_gives_prime_mul_sq` (35444907) then rebuilds `a = t * x ^ 2`
-- from exactly that datum.  `two_prime_odd_multiplicity_primes_of_a` (89d076b4)
-- identifies `t` as `q` or `r`.
--
-- Diagnostic notes.  The published binders are Bool coercions, so `a != 0` is
-- `(a != 0) = true` and each is recovered with `simpa`.  `Even e` unfolds to
-- `∃ k, e = k + k`; it is used as an ordinary `Prop` here because the sibling
-- hypothesis is the same shape.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_two_prime_odd_mult_unique_of_both_non_square
import Theorems.Thm_OddPerfectNumber_Kernel_odd_mult_single_gives_prime_mul_sq
import Theorems.Thm_OddPerfectNumber_Kernel_two_prime_odd_multiplicity_primes_of_a

namespace OddPerfectNumber.Kernel
namespace Blk

theorem solution_aux {a b q r : Nat} (ha0 : a != 0) (hb0 : b != 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q != r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a)
    (hnb : ¬ ∃ y, y ^ 2 = b) :
    exists t x : Nat, t.Prime /\ a = t * x ^ 2 /\ (t = q \/ t = r) := by
  classical
  have ha0' : a ≠ 0 := by simpa using ha0
  have hb0' : b ≠ 0 := by simpa using hb0
  have hqr' : q ≠ r := by simpa using hqr
  have hna' : ¬ (∃ y, y ^ 2 = a) := by simpa using hna
  have hnb' : ¬ (∃ y, y ^ 2 = b) := by simpa using hnb
  -- The unique odd-multiplicity prime of `a`.
  obtain ⟨t, ht, ht0, hall⟩ :=
    two_prime_odd_mult_unique_of_both_non_square ha0 hb0 hab hq hr hqr hsq hna hnb
  -- The parent child hands back the ordinary `Prop` `¬ Even (a.factorization t)`,
  -- while `odd_mult_single_gives_prime_mul_sq` takes the Bool negation
  -- `! Even (a.factorization t)`, i.e. `! decide (Even (a.factorization t)) = true`.
  -- Keep both forms: `ht0p` is the `Prop`, `ht0'` the `Bool` coercion.
  have ht0p : ¬ Even (a.factorization t) := ht0
  have ht0' : ! Even (a.factorization t) := by simpa using ht0p
  -- Rebuild `a` from its factorisation.
  obtain ⟨x, hx⟩ := odd_mult_single_gives_prime_mul_sq ha0 ht ht0' hall
  -- The unique defect is one of the two container primes.
  have hmem : t ∈ a.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    intro hc
    rw [hc] at ht0p
    exact ht0p (by simp)
  have htd : t ∣ a := Nat.dvd_of_mem_primeFactors hmem
  rcases two_prime_odd_multiplicity_primes_of_a ha0' hb0' hab hq hr hqr' hsq t ht htd ht0p
    with hq' | hr'
  · exact ⟨q, x, hq, by rw [hx, hq'], Or.inl rfl⟩
  · exact ⟨r, x, hr, by rw [hx, hr'], Or.inr rfl⟩

end Blk
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {a b q r : Nat} (ha0 : a != 0) (hb0 : b != 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q != r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a)
    (hnb : ¬ ∃ y, y ^ 2 = b) :
    exists t x : Nat, t.Prime /\ a = t * x ^ 2 /\ (t = q \/ t = r) :=
  OddPerfectNumber.Kernel.Blk.solution_aux ha0 hb0 hab hq hr hqr hsq hna hnb
