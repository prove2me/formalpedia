-- Prove2me | solution 1 for SemigroupBetti.GenData.coeff_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:21.415329+00:00
-- url     : https://prove2.me/submissions/b5bd3ea1-57e8-4874-871e-9ff5553bf9aa

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_toricMap_monomial
public import Theorems.Thm_SemigroupBetti_GenData_mem_toricKer
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
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
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution {f : MvPolynomial (Fin 4) K} (hf : f ∈ G.toricKer K) (d : ℕ) :
    ∑ s ∈ f.support.filter (fun s : Fin 4 →₀ ℕ => G.nu ⇑s = d), f.coeff s = 0 := by
  have hφ := (G.mem_toricKer K).1 hf
  rw [f.as_sum, map_sum] at hφ
  have := congrArg (fun p : Polynomial K => p.coeff d) hφ
  simp only [toricMap_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_filter]
  simpa [nu, eq_comm] using this
end SemigroupBetti.GenData
