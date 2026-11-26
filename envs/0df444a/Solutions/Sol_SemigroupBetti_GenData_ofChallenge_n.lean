-- Prove2me | solution 1 for SemigroupBetti.GenData.ofChallenge_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:01:31.870832+00:00
-- url     : https://prove2.me/submissions/300c1c6f-d685-40a7-9cce-bd5c3e3857c0

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
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
variable (n : Fin 4 → ℕ) (hpos : 0 < n 0) (hmono : StrictMono n)
  (hgcd : Finset.univ.gcd n = 1)
  (hmin : ∀ i : Fin 4, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i}))
namespace SemigroupBetti.GenData
theorem _root_.solution : (ofChallenge n hpos hmono hgcd hmin).n = n := by
  have h01 : n 0 < n 1 := hmono (by decide)
  have h12 : n 1 < n 2 := hmono (by decide)
  have h23 : n 2 < n 3 := hmono (by decide)
  funext i; fin_cases i <;> simp [GenData.n, gens, ofChallenge] <;> omega
end SemigroupBetti.GenData
