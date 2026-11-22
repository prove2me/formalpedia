-- Prove2me | solution 1 for UlmsTheorem.ulmSubgroup_add_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:27.801629+00:00
-- url     : https://prove2.me/submissions/1a483d04-2926-4733-8463-44cafb4db4c7

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_nat_iff
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
theorem _root_.solution (α : Ordinal) (n : ℕ) :
    ulmSubgroup p (α + n) (G := G) =
      { x | ∃ y ∈ ulmSubgroup p α (G := G), p ^ n • y = x } := by
  ext x
  exact mem_ulmSubgroup_add_nat_iff (p := p) (G := G) α n x
end UlmsTheorem
