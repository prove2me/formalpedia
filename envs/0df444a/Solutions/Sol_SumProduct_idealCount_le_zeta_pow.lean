-- Prove2me | solution 1 for SumProduct.idealCount_le_zeta_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:17.352751+00:00
-- url     : https://prove2.me/submissions/958f6fd6-7468-4054-b4da-b506feed1207

import Mathlib
import Definitions.Def_SumProduct_EulerBound
import Theorems.Thm_SumProduct_idealCount_prime_pow_le
import Theorems.Thm_SumProduct_zeta_pow_apply_prime_pow
import Theorems.Thm_SumProduct_idealCountArith_apply_ne
import Theorems.Thm_SumProduct_isMultiplicative_idealCountArith
import Theorems.Thm_SumProduct_isMultiplicative_zeta_pow
attribute [local simp] SumProduct.idealCountArith_apply_ne

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    idealCount K n
      ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (Module.finrank ℚ K)) n := by
  rw [← idealCountArith_apply_ne (K := K) hn,
    isMultiplicative_idealCountArith.multiplicative_factorization _ hn,
    (isMultiplicative_zeta_pow _).multiplicative_factorization _ hn,
    Finsupp.prod, Finsupp.prod]
  apply Finset.prod_le_prod'
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
  rw [idealCountArith_apply_ne (pow_ne_zero _ hpp.pos.ne'), zeta_pow_apply_prime_pow hpp]
  exact idealCount_prime_pow_le hpp _
end SumProduct
