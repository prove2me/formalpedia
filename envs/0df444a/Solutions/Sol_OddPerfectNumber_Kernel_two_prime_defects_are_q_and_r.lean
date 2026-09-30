-- Prove2me | solution 1 for OddPerfectNumber.Kernel.two_prime_defects_are_q_and_r
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T09:44:58.124261+00:00
-- url     : https://prove2.me/submissions/3e1cc312-9693-40da-b678-8fd6b0eb7afa

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
--
-- The contextual singleton-parity allocation for the `omega = 2` residual.
--
-- In the k = 5 two-prime case the first Dris equation reduces to
-- `m ^ 2 = d1 ^ 2 * (q * r * U * V)`, so `q * r * U * V` is a square.  Writing
-- `a = U` and `b = V`, the proved `two_prime_block_defects_differ` (bde45950)
-- supplies *distinct* primes `ta | a` and `tb | b`, each with an odd
-- factorisation exponent, and the proved `two_prime_odd_multiplicity_primes_of_a`
-- (89d076b4) confines each of them to `{q, r}`.  Two distinct members of
-- `{q, r}` are the two members in some order: that is the exact orientation
-- split the k = 5 residual needs.
--
-- The general claim "coprime non-squares have one odd-multiplicity prime each"
-- is false (`a = 15`, `b = 77` is a counterexample) and is *not* used: the
-- square relation `q * r * a * b = y ^ 2` is essential, and it is what
-- `two_prime_block_defects_differ` consumes.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_two_prime_block_defects_differ
import Theorems.Thm_OddPerfectNumber_Kernel_two_prime_odd_multiplicity_primes_of_a

open OddPerfectNumber.Kernel

namespace OddPerfectNumber.Kernel
namespace TwoPrimeDefects

theorem solution_aux {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a)
    (hnb : ¬ ∃ y, y ^ 2 = b) :
    ∃ x y : Nat, (x = q ∧ y = r) ∨ (x = r ∧ y = q) := by
  obtain ⟨ta, tb, hta, htb, tad, tbd, hta0, htb0, hne⟩ :=
    OddPerfectNumber.Kernel.two_prime_block_defects_differ ha0 hb0 hab hq hr hqr hsq hna hnb
  -- REPAIR (candidate 5016, remote 8015fa8b, CE at lines 44/45/46).  Two
  -- independent faults, both mechanical:
  --   * `two_prime_odd_multiplicity_primes_of_a` is stated with the *first* block
  --     named `a`, and its ninth argument is `t ∣ a`.  Passing `tb` with `tbd : tb ∣ b`
  --     is therefore a type mismatch, and Lean said so verbatim.  The fix is to
  --     apply it a second time with the two blocks swapped, which is legitimate
  --     because `Nat.gcd a b = Nat.gcd b a`, the square relation is symmetric up
  --     to commutativity, and `q ≠ r` is symmetric.
  --   * `hne : ta = tb → False` is a function, so `hne.trans` looks for a `trans`
  --     *field* on it and reports `Invalid field 'trans'`.  Function composition
  --     is `Function.comp`, or simply `fun h => hne (htaq.trans htbq.symm)`.
  have hsq' : ∃ y, y ^ 2 = q * r * b * a := by
    obtain ⟨y, hy⟩ := hsq
    -- REPAIR (30 September 2026 session H).  Remote 89aeb3fb returned the goal
    -- verbatim as `b * (q * r * a) = q * r * b * a`, so the single
    -- `Nat.mul_comm _ _` rewrite was not enough: after `rw [hy]` the two sides
    -- are commutatively *associated* as well as permuted, and one swap cannot
    -- rebracket `b * (q * r * a)`.  `ring` normalises the whole product.
    exact ⟨y, by rw [hy]; ring⟩
  have hba : Nat.gcd b a = 1 := by
    rw [Nat.gcd_comm]
    exact hab
  -- The confinement is applied by destructuring the disjunctions directly rather
  -- than through untyped `have`s, so no argument is left as a metavariable.
  rcases OddPerfectNumber.Kernel.two_prime_odd_multiplicity_primes_of_a
    ha0 hb0 hab hq hr hqr hsq ta hta tad hta0 with htaq | htar
  · rcases OddPerfectNumber.Kernel.two_prime_odd_multiplicity_primes_of_a
      hb0 ha0 hba hq hr hqr hsq' tb htb tbd htb0 with htbq | htbr
    · exact absurd htaq (fun h => hne (htaq.trans htbq.symm))
    · exact ⟨ta, tb, Or.inl ⟨htaq, htbr⟩⟩
  · rcases OddPerfectNumber.Kernel.two_prime_odd_multiplicity_primes_of_a
      hb0 ha0 hba hq hr hqr hsq' tb htb tbd htb0 with htbq | htbr
    · exact ⟨ta, tb, Or.inr ⟨htar, htbq⟩⟩
    · exact absurd htar (fun h => hne (htar.trans htbr.symm))

end TwoPrimeDefects
end OddPerfectNumber.Kernel

theorem solution {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a)
    (hnb : ¬ ∃ y, y ^ 2 = b) :
    ∃ x y : Nat, (x = q ∧ y = r) ∨ (x = r ∧ y = q) :=
  OddPerfectNumber.Kernel.TwoPrimeDefects.solution_aux ha0 hb0 hab hq hr hqr hsq hna hnb
