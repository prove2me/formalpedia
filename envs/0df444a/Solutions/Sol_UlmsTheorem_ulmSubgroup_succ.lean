-- Prove2me | solution 1 for UlmsTheorem.ulmSubgroup_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:20.206577+00:00
-- url     : https://prove2.me/submissions/00c85bdf-952e-4a03-a92b-38cf00a0d648

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_add_one
public import Theorems.Thm_UlmsTheorem_mem_pImage
attribute [local simp] UlmsTheorem.mem_pImage


attribute [local simp] UlmsTheorem.ulmSubgroup_zero

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) = pImage p (ulmSubgroup p α) := by
  simpa using ulmSubgroup_add_one p (G := G) α
end UlmsTheorem
