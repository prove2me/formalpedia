-- Prove2me | solution 1 for OddPerfectNumber.Kernel.two_prime_odd_mult_unique_of_both_non_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T15:41:37.767698+00:00
-- url     : https://prove2.me/submissions/6c4a859a-c360-446d-9f79-db575e69bb92

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.two_prime_odd_mult_unique_of_both_non_square
--          4308037b-5f4a-4a25-ad4f-1630244757b0
--
-- The singleton counting step.  In the square relation `y^2 = q * r * a * b`
-- with `gcd a b = 1`, distinct primes `q`, `r`, and both blocks non-square, the
-- odd-multiplicity support of `a` is a singleton lying in `{q, r}`.
--
-- Pure counting.  Each block has a defect prime (`odd_mult_prime_exists`) and
-- each defect lies in `{q, r}` (`two_prime_odd_multiplicity_primes_of_a`,
-- applied to `a` and to `b` with the blocks exchanged).  Coprimality forces the
-- two defects to differ, so they are exactly the two members of `{q, r}`.  Any
-- further odd-multiplicity prime of `a` would be the defect of `b`, dividing
-- both blocks, which coprimality forbids.
--
-- Diagnostic notes.  The published binders are Bool coercions: `a != 0` is
-- `(a != 0) = true`, recovered with `simpa`.  A prime never divides `1`, which
-- is `Nat.Prime.not_dvd_one`; `Nat.le_of_dvd` and friends do not exist under
-- those names in this revision.  A prime with odd multiplicity in `a` is a
-- member of `a.primeFactors` because an odd value is nonzero, and
-- `Nat.support_factorization` identifies the support with `a.primeFactors`.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_two_prime_odd_multiplicity_primes_of_a
import Theorems.Thm_OddPerfectNumber_Kernel_odd_mult_prime_exists

namespace OddPerfectNumber.Kernel
namespace Uniq

/-- The odd-multiplicity primes of `b` lie in `{q, r}`: the container lemma with
the two blocks exchanged.  Symmetry of the square relation is obtained by
associativity followed by an explicit commutation, because `q * r * a * b` is
grouped as `q * r * (a * b)`. -/
theorem b_defect_in_qr {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (t : Nat) (ht : t.Prime) (htd : t ∣ b)
    (ht0 : ¬ Even (b.factorization t)) : t = q ∨ t = r := by
  obtain ⟨y, hy⟩ := hsq
  have hsym : ∃ y, y ^ 2 = q * r * b * a :=
    ⟨y, by
      calc y ^ 2 = q * r * a * b := hy
        _ = q * r * (a * b) := by ring
        _ = q * r * (b * a) := by rw [Nat.mul_comm a b]
        _ = q * r * b * a := by ring⟩
  have hcomm : Nat.gcd b a = 1 := by simpa only [Nat.gcd_comm] using hab
  exact two_prime_odd_multiplicity_primes_of_a hb0 ha0 hcomm hq hr hqr hsym t ht htd ht0

theorem solution_aux {a b q r : Nat} (ha0 : a != 0) (hb0 : b != 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q != r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a)
    (hnb : ¬ ∃ y, y ^ 2 = b) :
    exists t : Nat, t.Prime /\ ¬ Even (a.factorization t) /\
      (forall z : Nat, z != t -> Even (a.factorization z)) := by
  classical
  have ha0' : a ≠ 0 := by simpa using ha0
  have hb0' : b ≠ 0 := by simpa using hb0
  have hqr' : q ≠ r := by simpa using hqr
  have hna' : ¬ (∃ y : Nat, y ^ 2 = a) := by simpa using hna
  have hnb' : ¬ (∃ y : Nat, y ^ 2 = b) := by simpa using hnb
  -- Each block has a defect prime, and each defect lies in the two-element set.
  obtain ⟨t, ht, htd, ht0⟩ := odd_mult_prime_exists ha0' hna'
  obtain ⟨tb, htb, htb0, htb1⟩ := odd_mult_prime_exists hb0' hnb'
  have htin : t = q ∨ t = r :=
    two_prime_odd_multiplicity_primes_of_a ha0' hb0' hab hq hr hqr' hsq t ht htd ht0
  have hbtin : tb = q ∨ tb = r := b_defect_in_qr ha0' hb0' hab hq hr hqr' hsq tb htb htb0 htb1
  -- Coprimality separates the two defects: `t` divides both blocks, so it
  -- divides their gcd, which is `1`, and a prime never divides `1`.
  have htbne : t ≠ tb := by
    intro hc
    subst hc
    have hgd : t ∣ Nat.gcd a b := Nat.dvd_gcd htd htb0
    rw [hab] at hgd
    exact ht.not_dvd_one hgd
  -- Distinct members of the two-element set `{q, r}` are `q` and `r` in some
  -- order, so the two defects are exactly the two container primes.
  have hpair : (t = q ∧ tb = r) ∨ (t = r ∧ tb = q) := by
    rcases htin with htq | htr
    · rcases hbtin with htbq | htbr
      -- `t = q` and `tb = q` force `t = tb`, which coprimality forbids.
      · exact absurd htbq (fun _ => htbne (htq.trans htbq.symm))
      · exact Or.inl ⟨htq, htbr⟩
    · rcases hbtin with htbq | htbr
      · exact Or.inr ⟨htr, htbq⟩
      -- `t = r` and `tb = r` force `t = tb` in exactly the same way.
      · exact absurd htbr (fun _ => htbne (htr.trans htbr.symm))
  have hall : forall z : Nat, z != t -> Even (a.factorization z) := by
    intro z hzb
    have hz : z ≠ t := by simpa using hzb
    by_contra hze
    have hz0 : a.factorization z ≠ 0 := by
      rintro hc
      rw [hc] at hze
      simp at hze
    have hmem : z ∈ a.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      exact hz0
    have hzprime : z.Prime := Nat.prime_of_mem_primeFactors hmem
    have hzd : z ∣ a := Nat.dvd_of_mem_primeFactors hmem
    have hz_odd : ¬ Even (a.factorization z) := hze
    have hzin : z = q ∨ z = r :=
      two_prime_odd_multiplicity_primes_of_a ha0' hb0' hab hq hr hqr' hsq z hzprime hzd hz_odd
    -- The defects are `q` and `r` in some order, so `{q, r} = {t, tb}` and the
    -- third member `z` equals `t` or `tb`.  The first contradicts `z != t`; the
    -- second makes `z` divide both blocks, which coprimality forbids.
    rcases hpair with ⟨htq, htbr⟩ | ⟨htr, htbq⟩
    · rcases hzin with hzq | hzr
      · exact hz (hzq.trans htq.symm)
      · have hztb : z = tb := hzr.trans htbr.symm
        have hztb0 : z ∣ b := by rwa [hztb]
        have hgd : z ∣ Nat.gcd a b := Nat.dvd_gcd hzd hztb0
        rw [hab] at hgd
        exact hzprime.not_dvd_one hgd
    · rcases hzin with hzq | hzr
      · have hztb : z = tb := hzq.trans htbq.symm
        have hztb0 : z ∣ b := by rwa [hztb]
        have hgd : z ∣ Nat.gcd a b := Nat.dvd_gcd hzd hztb0
        rw [hab] at hgd
        exact hzprime.not_dvd_one hgd
      · exact hz (hzr.trans htr.symm)
  exact ⟨t, ht, ht0, hall⟩

end Uniq
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {a b q r : Nat} (ha0 : a != 0) (hb0 : b != 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q != r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a)
    (hnb : ¬ ∃ y, y ^ 2 = b) :
    exists t : Nat, t.Prime /\ ¬ Even (a.factorization t) /\
      (forall z : Nat, z != t -> Even (a.factorization z)) :=
  OddPerfectNumber.Kernel.Uniq.solution_aux ha0 hb0 hab hq hr hqr hsq hna hnb
