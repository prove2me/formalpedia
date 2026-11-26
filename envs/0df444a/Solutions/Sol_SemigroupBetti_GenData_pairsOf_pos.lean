-- Prove2me | solution 1 for SemigroupBetti.GenData.pairsOf_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:17:30.633721+00:00
-- url     : https://prove2.me/submissions/6a45b8f7-cf9c-4296-b409-0f83d68ac663

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_pos
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
theorem _root_.solution {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) :
    ∀ x ∈ G.pairsOf F K i k, 1 ≤ x.1 ∧ 1 ≤ x.2 := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro x hx
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  exact ⟨G.sel_pos (hF d hd) hK (by rw [hKe]; simp),
    G.sel_pos (hF d hd) hK (by rw [hKe]; simp)⟩
end SemigroupBetti.GenData
