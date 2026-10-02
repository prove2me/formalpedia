-- Prove2me | solution 1 for OddPerfectNumber.Kernel.index_prime_has_non_self_sigma_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T16:11:56.113576+00:00
-- url     : https://prove2.me/submissions/143d8024-b24a-4db9-90b4-c3be7bb88314

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- A prime dividing `sigma(m^2)` is supplied by a DIFFERENT prime factor of `m`.
--
-- The `h2` source lever for the hard residual `five_no_two_prime_squarefree_index`,
-- applied to the kernel primes `q` and `r` rather than to `p`.
--
-- The accepted `exists_p_source_of_dvd` produces the source prime and the local
-- geometric sum.  The only new content is the non-self conclusion `t != q`: a
-- prime never divides its own sigma factor, because `sigma(q^(2a)) =
-- 1 + q + ... + q^(2a)` is `1 (mod q)`.  The Proved
-- `prime_not_dvd_own_sigma_prime_pow` (658bb7bb) states exactly this.
--
-- This does NOT show that the sources for `q` and `r` are distinct from each
-- other; a third prime could supply both.  That configuration stays open.
--
-- Diagnostic history, so it is not repeated:
--   5635 E02 `Function expected at htP / Actual type: Nat.Prime t` --
--     `htP` is the extracted PRIMALITY component of `Nat.mem_primeFactors`, so
--     it is a `Nat.Prime t` VALUE and cannot be applied.  The final step wrongly
--     wrote `htP (prime_not_dvd_own_sigma_prime_pow q ...)`.
--   5635 E01 `Application type mismatch ... of sort Prop but is expected to have
--     type of sort Type` at line 88 --
--     `Nat.mul_le_mul_left` is used with the bound as an IMPLICIT argument
--     `(k : Nat)` and the MULTIPLIER as the explicit one, i.e.
--     `Nat.mul_le_mul_left : 0 < k -> n * k <= n * m`.  Passing `hk2` positionally
--     as the first explicit argument therefore fed a `Prop` where a `Nat` was
--     expected.
--   5605 `Did not find an occurrence of the pattern t * k in the target t | k`
--     -- the `rw [<- hk]` rewrote in the wrong direction.
--   5516/5522 -- `Irreducible.eq_of_dvd_of_lt` and `Nat.Prime.lt_dvd` do not
--     exist, so the elementary `q = t * k` argument is used instead.
import Mathlib
import Theorems.Thm_OddPerfectNumber_exists_p_source_of_dvd
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

namespace OddPerfectNumber.Kernel
namespace IndexSource2

theorem solution_aux {m q : Nat} (hq : q.Prime)
    (hqm : Dvd.dvd q m) (hm2 : m ^ 2 != 0)
    (hrsig : Dvd.dvd q (∑ x ∈ (m ^ 2).divisors, x)) :
    exists t : Nat, t.Prime /\ Dvd.dvd t m /\ Not (Dvd.dvd t q) /\
      Dvd.dvd q (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) := by
  classical
  have hm2' : m ^ 2 ≠ 0 := by simpa using hm2
  have hq1 : q ^ 1 = q := by simp
  -- `exists_p_source_of_dvd` wants the hypothesis as `q ^ k | sigma(m^2)`, so the
  -- `Nat` divisibility `hrsig` is transported across `q ^ 1 = q` with a `rw`.
  have hpow : Dvd.dvd (q ^ 1) (∑ x ∈ (m ^ 2).divisors, x) := by
    rw [hq1]
    exact hrsig
  obtain ⟨t, htmem, htgeom⟩ :=
    OddPerfectNumber.exists_p_source_of_dvd q 1 m hq (by omega) hm2' hpow
  obtain ⟨htP, htdvd, _⟩ := (Nat.mem_primeFactors.mp htmem)
  -- `t | m ^ 2` with `t` prime gives `t | m` by `Prime.dvd_of_dvd_pow`, which is
  -- the direction the target's middle conjunct asks for.
  have htmdvd : Dvd.dvd t m := htP.dvd_of_dvd_pow htdvd
  refine ⟨t, htP, htmdvd, ?_, htgeom⟩
  -- `htP : Nat.Prime t` is a VALUE, so it cannot be applied (candidate 5635
  -- reported `Function expected at htP / Actual type: Nat.Prime t`).
  --
  -- Verified exact signature of the Proved helper (UUID 658bb7bb, fetched from the
  -- platform rather than guessed):
  --
  --   OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow (q a : Nat) (hq : q.Prime) :
  --     Not (q | sum i in range (a + 1), q ^ i)
  --
  -- Arity THREE, PRIME first and EXPONENT second: candidate 5697 reported
  -- `Expected type: Nat.Prime ((m ^ 2).factorization t)` when the arguments were
  -- swapped.  Instantiating at `t` gives directly the NON-DIVISIBILITY of `t` into
  -- its OWN sigma factor -- no `htq` assumption is needed, because `t` being prime
  -- already rules out `t | t`.
  have hself :
      Not (Dvd.dvd t (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i)) :=
    OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow
      t ((m ^ 2).factorization t) htP
  -- The goal is `Not (Dvd.dvd t q)`.  `t | q` with `q` PRIME gives `t = 1` or
  -- `t = q` (Nat.dvd_prime), and `t = 1` is impossible for a prime (two_le).  So
  -- `t | q` forces `t = q`, and then `htgeom` (which says `q` divides the `t`-indexed
  -- sum) becomes `t` dividing its OWN sigma factor, contradicting `hself`.
  --
  -- This avoids both `Nat.mul_le_mul_left` (three wasted rounds) and the
  -- `Nat.ModEq` detour.  `intro htq` turns the `Not` goal into the divisibility `t | q`.
  intro htq
  rcases (Nat.dvd_prime hq).mp htq with h1 | h2
  · -- `t = 1` contradicts `t` prime (a prime is at least 2).
    have htk : 2 <= t := htP.two_le
    exact absurd h1 (by omega)
  · -- `h2 : t = q`.  Substitute it, so `htgeom` reads `t | sum i ..., t ^ i`, which
    -- is exactly the statement `hself` denies.
    subst h2
    exact hself htgeom

end IndexSource2
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {m q : Nat} (hq : q.Prime)
    (hqm : Dvd.dvd q m) (hm2 : m ^ 2 != 0)
    (hrsig : Dvd.dvd q (∑ x ∈ (m ^ 2).divisors, x)) :
    exists t : Nat, t.Prime /\ Dvd.dvd t m /\ Not (Dvd.dvd t q) /\
      Dvd.dvd q (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) :=
  OddPerfectNumber.Kernel.IndexSource2.solution_aux hq hqm hm2 hrsig
