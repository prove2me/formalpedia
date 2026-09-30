-- Prove2me | solution 1 for OddPerfectNumber.Kernel.two_prime_block_defects_differ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:55:17.680966+00:00
-- url     : https://prove2.me/submissions/2472b68d-a1e6-4df5-8659-8d99faf2abef

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
--
-- `two_prime_block_defects_differ` (bde45950-5a45-4417-b317-f6a1f1690a26).
--
-- The contextual `k = 5` two-prime allocation step.  For a `q * r` square with
-- `gcd a b = 1` and both blocks non-square, every odd-multiplicity prime of `a`
-- lies in `{q, r}` (accepted child `two_prime_odd_multiplicity_primes_of_a`),
-- and likewise for `b` by applying that child to the exchanged pair.
-- Coprimality then forces the two defect primes to differ.
--
-- This repairs the predecessor (candidate 4660) at exactly its two first-causal
-- faults; both are recorded in place below.  The mathematics is unchanged.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_isSq_iff_even_factorization
import Theorems.Thm_OddPerfectNumber_Kernel_two_prime_odd_multiplicity_primes_of_a

namespace OddPerfectNumber.Kernel
namespace TwoPrimeB

/-- A non-square has a prime of odd multiplicity.  Mathlib has no `IsSquare` on
`Nat`, so squares are phrased as `∃ y, y ^ 2 = n` to match the surrounding
children.  The accepted bridge turns "every multiplicity is even" into "is a
square", so a non-square has an odd one; an odd value is nonzero, hence lies in
the support of `a.factorization`, which is `a.primeFactors` by
`Nat.support_factorization`. -/
theorem odd_mult_prime_exists' {a : Nat} (ha0 : a ≠ 0) (hna : ¬ ∃ y, y ^ 2 = a) :
    ∃ t : Nat, t.Prime ∧ t ∣ a ∧ ¬ Even (a.factorization t) := by
  classical
  have hnotall : ∃ p : Nat, ¬ Even (a.factorization p) := by
    by_contra hcon
    push_neg at hcon
    exact hna ((isSq_iff_even_factorization ha0).mpr hcon)
  obtain ⟨t, ht0⟩ := hnotall
  have htne : a.factorization t ≠ 0 := by
    intro hc
    -- `hc : a.factorization t = 0` is an equation with `a.factorization t` on
    -- the left, which is *not* a variable or a bare numeral, so `subst`
    -- rejects it.  `rw [hc]` performs the same substitution as a rewrite.
    rw [hc] at ht0
    exact ht0 (by simp)
  have hmem : t ∈ a.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact htne
  exact ⟨t, Nat.prime_of_mem_primeFactors hmem, Nat.dvd_of_mem_primeFactors hmem, ht0⟩

/-- The odd-multiplicity primes of `b` lie in `{q, r}`: the container lemma with
the two blocks exchanged. -/
theorem b_defect_in_qr {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (t : Nat) (ht : t.Prime) (htd : t ∣ b)
    (ht0 : ¬ Even (b.factorization t)) : t = q ∨ t = r := by
  obtain ⟨y, hy⟩ := hsq
  have hsym : ∃ y, y ^ 2 = q * r * b * a :=
    -- `Nat.mul_comm b a` cannot fire on `q * r * a * b` because the trailing
    -- product is grouped as `(a * b)`, not `b * a`.  Associativity is moved
    -- first so the commutation has a pattern to match.
    ⟨y, by
      calc y ^ 2 = q * r * a * b := hy
        _ = q * r * (a * b) := by ring
        _ = q * r * (b * a) := by rw [Nat.mul_comm a b]
        _ = q * r * b * a := by ring⟩
  -- FAULT 1 of the predecessor: `by rw [Nat.gcd_comm]` left the goal
  -- `a.gcd b = 1` open, because rewriting a hypothesis with `rw` only rewrites
  -- the goal and `Nat.gcd_comm` has no `a` on either side to match.  The
  -- required statement is `Nat.gcd b a = 1`, which is `hab` rewritten with the
  -- commutativity lemma; `simpa only [Nat.gcd_comm] using hab` states it
  -- directly and leaves nothing open.
  have hcomm : Nat.gcd b a = 1 := by simpa only [Nat.gcd_comm] using hab
  exact two_prime_odd_multiplicity_primes_of_a hb0 ha0 hcomm hq hr hqr hsym t ht htd ht0

/-- The two blocks of a `q * r` square have different odd-multiplicity primes. -/
theorem block_defects_differ {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a)
    (hnb : ¬ ∃ y, y ^ 2 = b) :
    ∃ ta tb : Nat, ta.Prime ∧ tb.Prime ∧ ta ∣ a ∧ tb ∣ b ∧
      ¬ Even (a.factorization ta) ∧ ¬ Even (b.factorization tb) ∧ ta ≠ tb := by
  -- Both blocks are non-squares, so each has an odd-multiplicity prime.
  obtain ⟨ta, hta, hta0, hta1⟩ := odd_mult_prime_exists' ha0 hna
  obtain ⟨tb, htb, htb0, htb1⟩ := odd_mult_prime_exists' hb0 hnb
  -- Both defect primes lie in `{q, r}`.
  have hain : ta = q ∨ ta = r :=
    two_prime_odd_multiplicity_primes_of_a ha0 hb0 hab hq hr hqr hsq ta hta hta0 hta1
  have hbin : tb = q ∨ tb = r := b_defect_in_qr ha0 hb0 hab hq hr hqr hsq tb htb htb0 htb1
  -- Coprimality rules out `ta = tb`: `ta` would divide both blocks, hence their
  -- gcd, hence `1`.
  have hne : ta ≠ tb := by
    intro hc
    subst hc
    have hgd : ta ∣ Nat.gcd a b := Nat.dvd_gcd hta0 htb0
    rw [hab] at hgd
    -- FAULT 2 of the predecessor: `omega` was asked to close `False` from a
    -- `Nat.le_of_dvd` bound it could not connect, because the real content is
    -- that a prime is at least `2`.  `Nat.Prime.two_le` states exactly that, and
    -- `Nat.le_of_dvd` turns `ta ∣ 1` into `ta ≤ 1`.
    -- Neither `Nat.le_of_dvd`, `Nat.dvd_one` nor `Nat.le_of_dvd_one` exists under
    -- those names in the pinned revision (each was checked against the
    -- revision-keyed declaration index).  `Nat.Prime.not_dvd_one` is the
    -- statement that actually exists, and it contradicts `hgd` directly: a prime
    -- never divides the unit, yet `hgd` says `ta` does.
    exact hta.not_dvd_one hgd
  exact ⟨ta, tb, hta, htb, hta0, htb0, hta1, htb1, hne⟩

end TwoPrimeB
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a)
    (hnb : ¬ ∃ y, y ^ 2 = b) :
    ∃ ta tb : Nat, ta.Prime ∧ tb.Prime ∧ ta ∣ a ∧ tb ∣ b ∧
      ¬ Even (a.factorization ta) ∧ ¬ Even (b.factorization tb) ∧ ta ≠ tb :=
  OddPerfectNumber.Kernel.TwoPrimeB.block_defects_differ ha0 hb0 hab hq hr hqr hsq hna hnb
