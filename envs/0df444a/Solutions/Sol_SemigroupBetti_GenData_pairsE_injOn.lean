-- Prove2me | solution 1 for SemigroupBetti.GenData.pairsE_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:18:03.398655+00:00
-- url     : https://prove2.me/submissions/7cc2ef7c-0820-44f0-8221-46161172bb7e

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_isSplit12_of_mem_famE
public import Theorems.Thm_SemigroupBetti_GenData_sel12_le_iff
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
theorem _root_.solution : Set.InjOn (fun d => (G.sel d {1, 2} 1, G.sel d {1, 2} 2)) G.famE := by
  intro d hd d' hd' h
  simp only [Prod.mk.injEq] at h
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  have hle := (G.sel12_le_iff hd hd').2 ⟨h.1.le, h.2.le⟩
  have hge := (G.sel12_le_iff hd' hd).2 ⟨h.1.ge, h.2.ge⟩
  rw [← (G.sel_of_split (G.isSplit12_of_mem_famE hd) hK).1,
    ← (G.sel_of_split (G.isSplit12_of_mem_famE hd') hK).1, le_antisymm hle hge]
end SemigroupBetti.GenData
