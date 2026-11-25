-- Prove2me | solution 1 for UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:54.398882+00:00
-- url     : https://prove2.me/submissions/6c282065-4219-4181-ab12-b8d152c598cd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ProdPrimeFactorsPowCeilPadicValNatMulEqPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ (Q T a b : ℕ), Q ≠ 0 → ∏ p ∈ Q.primeFactors.filter Nat.Prime,
      p ^ (T * ⌈(padicValNat p Q : ℝ) * (a : ℝ)⌉.toNat + ⌈(padicValNat p Q : ℝ) * (b : ℝ)⌉.toNat) = Q ^ (T * a + b) := by
  intro Q T a b hQ
  have hc : ∀ m n : ℕ, ⌈(m : ℝ) * (n : ℝ)⌉.toNat = m * n := by
    intro m n
    rw [← Nat.cast_mul, Int.ceil_natCast, Int.toNat_natCast]
  have hf : Q.primeFactors.filter Nat.Prime = Q.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  have hQ' : ∏ p ∈ Q.primeFactors, p ^ (Q.factorization p) = Q := by
    have := Nat.factorization_prod_pow_eq_self hQ
    rwa [Finsupp.prod, Nat.support_factorization] at this
  rw [hf]
  conv_rhs => rw [← hQ', ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [hc, hc, ← pow_mul, Nat.factorization_def Q (Nat.prime_of_mem_primeFactors hp)]
  congr 1
  ring
end UpperTheory
