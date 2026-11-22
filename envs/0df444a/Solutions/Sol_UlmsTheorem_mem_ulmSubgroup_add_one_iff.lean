-- Prove2me | solution 1 for UlmsTheorem.mem_ulmSubgroup_add_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:19.7313+00:00
-- url     : https://prove2.me/submissions/985f6c0f-c169-4568-a344-0f78f9ca1f2b

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_add_one
public import Theorems.Thm_UlmsTheorem_mem_pImage
attribute [local simp] UlmsTheorem.mem_pImage



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (α : Ordinal) (x : G) :
    x ∈ ulmSubgroup p (α + 1) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p • y = x := by
  rw [ulmSubgroup_add_one, mem_pImage]
end UlmsTheorem
