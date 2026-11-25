-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.sInf_F_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:04.29201+00:00
-- url     : https://prove2.me/submissions/6866d0d8-9462-4c3d-804a-069f8b7ce958

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_eq
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meetT_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_unop_op
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_op
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_prop
attribute [local simp] PretorsionImageClosed.Statement.PretorsionTheory.op_unop
attribute [local simp] PretorsionImageClosed.Statement.PretorsionTheory.unop_op
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_prop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_unop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.unop_op
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.unop_prop



set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C]
variable [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory
namespace PretorsionImageClosed.Statement.PretorsionTheory
theorem _root_.solution (S : Set (PretorsionTheory C)) :
    (sInf S).F.prop = ⨅ (F : Subcategory C)
      (_ : IsPretorsionTheory (⨅ P ∈ S, P.T.prop) F.prop ∧ ∀ P ∈ S, P.F.prop ≤ F.prop), F.prop := by
  rw [sInf_eq, ← meetT_prop]
  funext X
  apply propext
  show (Subcategory.iInf (fun F : MeetPartners S => F.1)).prop X ↔ _
  rw [iInf_prop_iff]
  simp only [iInf_apply, iInf_Prop_eq]
  exact ⟨fun h F hF => h ⟨F, hF⟩, fun h F => h F.1 F.2⟩
end PretorsionImageClosed.Statement.PretorsionTheory
