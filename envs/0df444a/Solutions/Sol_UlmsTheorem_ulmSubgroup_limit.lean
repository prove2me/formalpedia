-- Prove2me | solution 1 for UlmsTheorem.ulmSubgroup_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:06.382984+00:00
-- url     : https://prove2.me/submissions/d6508a63-309b-41c5-a2b5-67deecb0a436

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
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
theorem _root_.solution (o : Ordinal) (ho : Order.IsSuccLimit o) :
    ulmSubgroup p o (G := G) = ⨅ (β : Ordinal) (_ : β < o), ulmSubgroup p β := by
  unfold ulmSubgroup
  simpa using
    (Ordinal.limitRecOn_limit o
      (⊤ : AddSubgroup G)
      (fun _β Hβ ↦ pImage p Hβ)
      (fun o _ho IH ↦ ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)
      ho)
end UlmsTheorem
