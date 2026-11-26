-- Prove2me | solution 1 for SemigroupBetti.GenData.card_le_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:18:31.575873+00:00
-- url     : https://prove2.me/submissions/60de3386-63e7-4bd8-b4c5-0194ffcfc0ef

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_sel_coord_injOn
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
theorem _root_.solution {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ G.sel d K k ∧ G.sel d K k ≤ c) : F.card ≤ c := by
  have := card_le_card_of_injOn (fun d => G.sel d K k) (t := Icc 1 c)
    (fun d hd => mem_coe.2 (mem_Icc.2 (hc d (mem_coe.1 hd))))
    (G.sel_coord_injOn hik hKe F hF)
  simpa using this
end SemigroupBetti.GenData
