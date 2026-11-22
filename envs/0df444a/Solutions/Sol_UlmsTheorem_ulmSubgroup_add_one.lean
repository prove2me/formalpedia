-- Prove2me | solution 1 for UlmsTheorem.ulmSubgroup_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:53:48.858613+00:00
-- url     : https://prove2.me/submissions/f08bab72-e7eb-4233-abcf-78f2885edb6e

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
theorem _root_.solution (α : Ordinal) :
    ulmSubgroup p (α + 1) (G := G) = pImage p (ulmSubgroup p α) := by
  rw [ulmSubgroup, Ordinal.limitRecOn_add_one, ulmSubgroup]
end UlmsTheorem
