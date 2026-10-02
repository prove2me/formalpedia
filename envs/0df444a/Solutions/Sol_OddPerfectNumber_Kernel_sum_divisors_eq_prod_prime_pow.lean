-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sum_divisors_eq_prod_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T15:10:50.35314+00:00
-- url     : https://prove2.me/submissions/b0ffcad1-ff80-4896-b90c-28a6f1930e5b

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.sum_divisors_eq_prod_prime_pow
--          39086529-e011-424a-a470-218ae935c6a1
--
-- The divisor sum of `m ^ 2` is the product of the divisor `n := m ^ 2`.
--
-- Diagnostic history, so it is not repeated:
--   5637 E01 `Invalid argument name 'k' for Nat.Prime.dvd_of_dvd_pow` and E02
--     `Unknown identifier 'hk'` -- the hand-written support proof used
--     `rw [hk]; rfl` inside that application, which is malformed Lean.
--   5637 E03 `t | ?m ^ ?m` -- the same hand-written divisibility.
--   5637 E04 `rewrite failed ... in the target expression
--     range (2 * m.factorization t + 1) ... = sum d in (t ^ (2 * m.factorization t)).divisors, d`
--     -- `hmain` rewrote the exponent a SECOND time inside `Finset.prod_congr`,
--     after `hfac` had already fired.  Both rewrites are now fused into ONE
--     `Nat.sum_divisors_prime_pow` step on a stated `have`, so nothing is
--     rewritten twice.
--
-- Route.  Mathlib carries the decomposition
-- `ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul`,
-- whose usage is copied from the accepted `solution_sigma_cross_bound.lean:31`,
-- applied to `n := m ^ 2`.  The SUPPORT equality is the Mathlib lemma for exactly
-- this (`Nat.primeFactors_pow_succ m 1 : (m ^ (1 + 1)).primeFactors = m.primeFactors`),
-- so it is a single rewrite with no `Nat.mem_primeFactors` extensionality proof.
--
-- The accepted idiom for the local geometric sum is
-- `Nat.sum_divisors_prime_pow (f := fun x : Nat => x) hp (k := k)`, copied from the
-- accepted `solution_dris_packaged_parity_normalization_direct.lean:26`.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace SigmaProd2

theorem solution_aux {m : Nat} (hm0 : m != 0) :
    (∑ d ∈ (m ^ 2).divisors, d) =
      ∏ t ∈ m.primeFactors, (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) := by
  have hm0' : m ≠ 0 := by simpa using hm0
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0'
  -- Support of `m ^ 2` equals support of `m`: Mathlib's `Nat.primeFactors_pow`
  -- does this directly, so no `Nat.mem_primeFactors` extensionality is needed.
  have hsupp : (m ^ 2).primeFactors = m.primeFactors := by
    rw [show m ^ 2 = m ^ (1 + 1) by ring, Nat.primeFactors_pow_succ m 1]
  -- Every local divisor sum becomes a geometric sum, in ONE step per summand.
  have hgeom : ∀ t ∈ m.primeFactors,
      (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) =
        (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) := by
    intro t ht
    have hfac : (m ^ 2).factorization t = 2 * m.factorization t := by
      rw [Nat.factorization_pow, Finsupp.nsmul_apply, Nat.nsmul_eq_mul]
    rw [hfac]
    -- `Nat.sum_divisors_prime_pow hp k` reads
    --   (∑ d ∈ (q^k).divisors, d) = (∑ i ∈ range (k+1), q^i)
    -- and the goal has the geometric sum on the LEFT, so the needed term is the
    -- SYMMETRY.  Candidate 5494 applied `.symm` to the wrong side.
    exact Eq.symm
      (Nat.sum_divisors_prime_pow (f := fun x : Nat => x)
        (Nat.prime_of_mem_primeFactors ht) (k := 2 * m.factorization t))
  calc
    (∑ d ∈ (m ^ 2).divisors, d) = ArithmeticFunction.sigma 1 (m ^ 2) := by
      rw [← ArithmeticFunction.sigma_one_apply]
    _ = ∏ t ∈ (m ^ 2).primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i := by
      simpa only [mul_one] using
        ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) (n := m ^ 2) hsq0
    _ = ∏ t ∈ m.primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i := by
      rw [hsupp]
    _ = ∏ t ∈ m.primeFactors,
        (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) := by
      apply Finset.prod_congr rfl
      intro t ht
      exact hgeom t ht

end SigmaProd2
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {m : Nat} (hm0 : m != 0) :
    (∑ d ∈ (m ^ 2).divisors, d) =
      ∏ t ∈ m.primeFactors, (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) :=
  OddPerfectNumber.Kernel.SigmaProd2.solution_aux hm0
