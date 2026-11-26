-- Prove2me | solution 1 for SemigroupBetti.GenData.card_genSet_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:07:41.464903+00:00
-- url     : https://prove2.me/submissions/b7812595-bedc-4327-a962-95f9da8684a7

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
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution (d : ℕ) : #(G.genSet K d) ≤ G.ncomp d - 1 := by
  classical
  unfold genSet
  split_ifs with h
  · refine (card_image_le).trans ?_
    rw [card_erase_of_mem (mem_univ _), card_univ, ncomp]
  · simp
end SemigroupBetti.GenData
