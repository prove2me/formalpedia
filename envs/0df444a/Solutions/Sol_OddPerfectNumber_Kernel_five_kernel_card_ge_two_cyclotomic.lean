-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_kernel_card_ge_two_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T13:51:04.85879+00:00
-- url     : https://prove2.me/submissions/91175ec3-978f-4edf-8be3-b9095aa1aa6d

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
--
-- Phase E wrapper, corrected form.  The square-free part of the k = 5 Dris
-- index has at least two distinct prime factors.
--
-- The hypothesis `h1` is the first Dris equation with `sigma(p^5)` already
-- replaced by its proved factorisation
-- `2 * (p^2 + p + 1) * ((p+1)/2) * (p^2 - p + 1)`
-- (`five_sigma_two_cyclotomic_odd_prime`, 7f2041ff).  That is exactly what
-- `five_index_not_prime_mul_square` needs, so the exclusion applies directly.
--
-- Three accepted `Kernel` children are assembled:
--   * `sqfree_part_ne_one` (b59073fb): `d2 ≠ 1`, else `s = d1^2`;
--   * `five_index_not_prime_mul_square` (2ec27119): `d2` is not prime, else
--     `s = d1^2 * q` is a prime times a square;
--   * `squarefree_card_ge_two_of_not_one_or_prime` (9c90129e): the two
--     exclusions give the cardinality bound.
--
-- No coprimality between `d1` and `d2` is needed for either exclusion.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_sqfree_part_ne_one
import Theorems.Thm_OddPerfectNumber_Kernel_five_index_not_prime_mul_square
import Theorems.Thm_OddPerfectNumber_Kernel_squarefree_card_ge_two_of_not_one_or_prime
import Theorems.Thm_OddPerfectNumber_Kernel_five_sigma_two_cyclotomic_odd_prime

namespace OddPerfectNumber.Kernel
namespace KCard2Cyc

theorem solution_aux (p m s d1 d2 : Nat) (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m) (hs_nsq : ¬ ∃ r, s = r ^ 2)
    (hd2 : d1 ^ 2 * d2 = s) (hd2pos : 0 < d2) (hdsf : Squarefree d2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * s) :
    2 ≤ d2.primeFactors.card := by
  -- `d2 = 1` would make `s` a perfect square.
  have hne1 : d2 ≠ 1 := OddPerfectNumber.Kernel.sqfree_part_ne_one s d1 d2 hd2 hs_nsq
  -- A prime `d2` makes `s` a prime times the square `d1^2`; the published
  -- k = 5 exclusion rules that out from the first Dris equation alone.
  have hnePrime : ∀ q, q.Prime → d2 ≠ q := by
    intro q hq hd2q
    -- REPAIR (30 September 2026 session K, remote c043c227 CE at line 40).
    -- `five_index_not_prime_mul_square` states its Dris hypothesis with the
    -- *summation* `∑ d ∈ (p ^ 5).divisors, d`, whereas this target carries the
    -- already-factorised form.  The proved `five_sigma_two_cyclotomic_odd_prime`
    -- (7f2041ff) is exactly the bridge between the two spellings, so the
    -- factorised hypothesis is turned into the summation one by rewriting with
    -- it.  REPAIR 2 (remote f5c96575 CE at line 53): the target's `hp2` is
    -- *already* the `(p != 2) = true` shape that the proved factorisation
    -- takes, so passing a converted `p ≠ 2` was wrong.  `hp2` is used directly.
    -- REPAIR 3 (remote af1f33f2 CE at line 50): the proved factorisation is
    -- oriented factorised-equals-summation, so `hsum` states it in the *same*
    -- direction and is consumed with `rw [← hsum]`.
    have hsum : 2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) = (∑ d ∈ (p ^ 5).divisors, d) :=
      OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_odd_prime p hp hp2
    refine OddPerfectNumber.Kernel.five_index_not_prime_mul_square p m s q d1
      hp hp2 hp4 hm hpm hq ?_ ?_ ?_
    · -- `s = q * (d1)^2`
      rw [← hd2, hd2q]
      ring
    · -- REPAIR 4 (remote af1f33f2, `case refine_2`): the remaining goal order
      -- puts `0 < s` *before* the Dris equation, because `hspos` precedes `h1`
      -- in the target's binder list.  Each goal is therefore closed on its own.
      have hsq : s = q * d1 ^ 2 := by
        rw [← hd2, hd2q]
        ring
      rw [hsq]
      have hd1pos : 0 < d1 := by
        rcases Nat.eq_zero_or_pos d1 with hd1z | hd1p
        · have hz : s = 0 := by
            rw [← hd2, hd1z]
            ring
          exact absurd (hs_nsq ⟨0, hz⟩) (by simp)
        · exact hd1p
      -- REPAIR 5 (remote 3a85b172 CE at line 73): the pinned revision spells
      -- the prime positivity `Nat.Prime.pos`, not `Nat.prime_pos`, and
      -- `Nat.pow_pos` does not take a trailing exponent here, so the square
      -- positivity is obtained by rewriting `d1 ^ 2` as `d1 * d1`.
      -- REPAIR 6 (remote 2a927886 CE at line 78): that `rw` already rewrote the
      -- exponent and simplified `d1 ^ 1`, so the trailing `mul_one` had no
      -- `?a * 1` left to consume.  Only the exponent rewrite is kept.
      -- REPAIR 7 (remote 7e4e80aa CE at line 82): `pow_add` left the summand
      -- as `d1 ^ 1`, which is not syntactically `d1`, so `Nat.mul_pos` no longer
      -- applied.  `pow_succ` reduces the successor exponent directly and is
      -- followed by an explicit `pow_one` rewrite.
      have hsqpos : 0 < d1 ^ 2 := by
        rw [show (2 : Nat) = Nat.succ 1 by omega, pow_succ, pow_one]
        exact Nat.mul_pos hd1pos hd1pos
      exact Nat.mul_pos hq.pos hsqpos
    · -- the Dris equation, restated with the summation
      rw [← hsum]
      exact h1
  exact OddPerfectNumber.Kernel.squarefree_card_ge_two_of_not_one_or_prime
    hd2pos hdsf hne1 hnePrime

end KCard2Cyc
end OddPerfectNumber.Kernel

-- The target declares its binders inside `namespace OddPerfectNumber.Kernel`,
-- so the namespace must be opened for a top-level `theorem solution`.  Every
-- import above is a *Proved* child, so the namespace exists remotely.
open OddPerfectNumber.Kernel

theorem solution (p m s d1 d2 : Nat) (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m) (hs_nsq : ¬ ∃ r, s = r ^ 2)
    (hd2 : d1 ^ 2 * d2 = s) (hd2pos : 0 < d2) (hdsf : Squarefree d2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * s) :
    2 ≤ d2.primeFactors.card :=
  OddPerfectNumber.Kernel.KCard2Cyc.solution_aux p m s d1 d2 hp hp2 hp4 hm hpm hs_nsq
    hd2 hd2pos hdsf h1
