-- Prove2me | solution 1 for SemigroupBetti.GenData.exists_coord_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:18:51.551063+00:00
-- url     : https://prove2.me/submissions/d065cbd9-119c-4393-aa17-3e9b9871c073

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_coord_injOn
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
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ G.sel d K k ∧ G.sel d K k ≤ c) (hcard : F.card = c) {v : ℕ}
    (hv1 : 1 ≤ v) (hvc : v ≤ c) : ∃ d ∈ F, G.sel d K k = v := by
  obtain ⟨d, hd, h⟩ := surj_on_of_inj_on_of_card_le (s := F) (t := Icc 1 c)
    (fun d _ => G.sel d K k) (fun d hd => mem_Icc.2 (hc d hd))
    (fun d d' hd hd' h => G.sel_coord_injOn hik hKe F hF hd hd' h)
    (by simp [hcard]) v (mem_Icc.2 ⟨hv1, hvc⟩)
  exact ⟨d, hd, h.symm⟩
end SemigroupBetti.GenData
