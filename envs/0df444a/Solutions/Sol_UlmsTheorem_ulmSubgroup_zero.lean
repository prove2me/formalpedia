-- Prove2me | solution 1 for UlmsTheorem.ulmSubgroup_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:53:38.187083+00:00
-- url     : https://prove2.me/submissions/b18d0ef6-b2cf-4fed-b1a9-825a41091f66

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution : ulmSubgroup p (0 : Ordinal) (G := G) = ⊤ := by
  rw [ulmSubgroup, Ordinal.limitRecOn_zero]
end UlmsTheorem
