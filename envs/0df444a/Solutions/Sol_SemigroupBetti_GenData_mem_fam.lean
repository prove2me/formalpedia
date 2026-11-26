-- Prove2me | solution 1 for SemigroupBetti.GenData.mem_fam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:54:39.902279+00:00
-- url     : https://prove2.me/submissions/2f69b92f-c45d-4986-9a6e-12c191162212

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
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
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {K : Finset (Fin 4)} {d : ℕ} :
    d ∈ G.fam K ↔ d ≤ G.H ∧ G.contributes d ∧ ¬ G.HasSingletonComp d ∧ G.IsSplit d K := by
  classical
  unfold fam; simp only [mem_filter, mem_range, Nat.lt_succ_iff]
end SemigroupBetti.GenData
