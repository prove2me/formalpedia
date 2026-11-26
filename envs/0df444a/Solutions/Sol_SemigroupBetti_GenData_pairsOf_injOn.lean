-- Prove2me | solution 1 for SemigroupBetti.GenData.pairsOf_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:17:54.544067+00:00
-- url     : https://prove2.me/submissions/650d5d2e-5c10-41b6-8d5b-b90df6b8676f

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_sel_le_of_coords
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_of_split
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
    Set.InjOn (fun d => (G.sel d K i, G.sel d K k)) F := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro d hd d' hd' h
  simp only [Prod.mk.injEq] at h
  have hle := G.sel_le_of_coords hKe hK (hF d hd) (hF d' hd') h.1.le h.2.le
  have hge := G.sel_le_of_coords hKe hK (hF d' hd') (hF d hd) h.1.ge h.2.ge
  rw [← (G.sel_of_split (hF d hd) hK).1, ← (G.sel_of_split (hF d' hd') hK).1,
    le_antisymm hle hge]
end SemigroupBetti.GenData
