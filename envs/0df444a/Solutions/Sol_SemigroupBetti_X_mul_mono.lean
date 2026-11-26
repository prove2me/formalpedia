-- Prove2me | solution 1 for SemigroupBetti.X_mul_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:06:53.891948+00:00
-- url     : https://prove2.me/submissions/9ded88ae-a588-450a-bb7c-b4f8d2221428

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
variable (K : Type*) [Field K]
variable {K}
namespace SemigroupBetti
theorem _root_.solution (i : Fin 4) (u : Fin 4 → ℕ) :
    (X i : MvPolynomial (Fin 4) K) * mono K u = mono K (u + Pi.single i 1) := by
  rw [mono, mono, X, monomial_mul, one_mul]
  have : Finsupp.single i 1 + Finsupp.equivFunOnFinite.symm u =
      Finsupp.equivFunOnFinite.symm (u + Pi.single i 1) := by
    refine Finsupp.ext fun j => ?_
    by_cases h : j = i
    · subst h; simp [add_comm]
    · simp [h]
  rw [this]
end SemigroupBetti
