-- Prove2me | solution 1 for UlmsTheorem.map_ulmSubgroup_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:25.084888+00:00
-- url     : https://prove2.me/submissions/bd6d5e44-fde0-4c4d-9658-2d62db8d2055

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_add_one
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_limit_iff
public import Theorems.Thm_UlmsTheorem_mem_pImage
attribute [local simp] UlmsTheorem.mem_pImage


attribute [local simp] UlmsTheorem.ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution {H : Type*} [AddCommGroup H] (φ : G →+ H) (α : Ordinal) :
    (ulmSubgroup p α (G := G)).map φ ≤ ulmSubgroup p α (G := H) := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      simp [ulmSubgroup]
  | add_one α ih =>
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [ulmSubgroup_add_one] at hx ⊢
      rcases hx with ⟨z, hz, rfl⟩
      exact ⟨φ z, ih ⟨z, hz, rfl⟩, by simp⟩
  | limit o ho IH =>
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      change x ∈ ulmSubgroup p o at hx
      rw [mem_ulmSubgroup_limit_iff p ho] at hx ⊢
      intro β hβ
      exact IH β hβ ⟨x, hx β hβ, rfl⟩
end UlmsTheorem
