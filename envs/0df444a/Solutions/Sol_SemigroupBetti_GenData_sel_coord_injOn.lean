-- Prove2me | solution 1 for SemigroupBetti.GenData.sel_coord_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:17:02.211837+00:00
-- url     : https://prove2.me/submissions/3badccbd-9b05-4709-9468-1eabdd7ba6be

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_antichain
public import Theorems.Thm_SemigroupBetti_GenData_sel_eq_zero
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
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) :
    Set.InjOn (fun d => G.sel d K k) F := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro d hd d' hd' h
  simp only at h
  by_contra hne
  have hle : ∀ {e e' : ℕ}, e ∈ F → e' ∈ F → G.sel e K k = G.sel e' K k →
      G.sel e K i ≤ G.sel e' K i → G.sel e K ≤ G.sel e' K := by
    intro e e' he he' hk hi j
    by_cases hj : j ∈ K
    · rw [hKe, mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hi
      · exact hk.le
    · rw [G.sel_eq_zero (hF e he) hK hj, G.sel_eq_zero (hF e' he') hK hj]
  rcases le_total (G.sel d K i) (G.sel d' K i) with hi | hi
  · exact G.sel_antichain hK (hF d hd) (hF d' hd') hne (hle hd hd' h hi)
  · exact G.sel_antichain hK (hF d' hd') (hF d hd) (Ne.symm hne) (hle hd' hd h.symm hi)
end SemigroupBetti.GenData
