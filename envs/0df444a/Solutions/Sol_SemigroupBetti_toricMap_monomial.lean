-- Prove2me | solution 1 for SemigroupBetti.toricMap_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:59:38.38934+00:00
-- url     : https://prove2.me/submissions/ff98eb55-4cbe-4c55-8a0f-38c4b612a245

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
variable (K : Type*) [Field K]
variable {K}
namespace SemigroupBetti
theorem _root_.solution (n : Fin 4 → ℕ) (s : Fin 4 →₀ ℕ) (c : K) :
    toricMap K n (monomial s c) = Polynomial.C c * Polynomial.X ^ (∑ i, s i * n i) := by
  rw [toricMap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_eq]
  congr 2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end SemigroupBetti
