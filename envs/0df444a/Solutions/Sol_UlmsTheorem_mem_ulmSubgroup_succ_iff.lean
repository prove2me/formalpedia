-- Prove2me | solution 1 for UlmsTheorem.mem_ulmSubgroup_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:56.512107+00:00
-- url     : https://prove2.me/submissions/35574d8e-d835-4b65-ac8e-a85279e5dcbc

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_succ
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
    x ∈ ulmSubgroup p (Order.succ α) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p • y = x := by
  rw [ulmSubgroup_succ, mem_pImage]
end UlmsTheorem
