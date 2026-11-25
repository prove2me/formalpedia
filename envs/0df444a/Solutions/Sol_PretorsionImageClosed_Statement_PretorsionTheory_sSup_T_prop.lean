-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.sSup_T_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:45.244347+00:00
-- url     : https://prove2.me/submissions/1fc2a1b1-6845-4285-bcc0-6403052c3fa7

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_eq_join
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meet_F
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_join_T
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meetT_op_image
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_unop_op
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_le_op_iff
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
    (sSup S).T.prop = ⨅ (T : Subcategory C)
      (_ : IsPretorsionTheory T.prop (⨅ P ∈ S, P.F.prop) ∧ ∀ P ∈ S, P.T.prop ≤ T.prop), T.prop := by
  rw [sSup_eq_join, join_T, meet_F]
  funext X
  apply propext
  rw [Subcategory.unop_prop, ObjectProperty.unop_iff, iInf_prop_iff]
  simp only [iInf_apply, iInf_Prop_eq]
  constructor
  · intro h T hT
    refine h ⟨T.op, ?_, ?_⟩
    · rw [meetT_op_image]
      exact hT.1.op
    · rintro _ ⟨P, hP, rfl⟩
      exact Subcategory.op_le_op_iff.2 (hT.2 P hP)
  · rintro h ⟨G, hG1, hG2⟩
    refine h G.unop ⟨?_, fun P hP => ?_⟩
    · rw [meetT_op_image] at hG1
      exact hG1.unop
    · have := hG2 P.op ⟨P, hP, rfl⟩
      rw [← Subcategory.op_unop G] at this
      exact Subcategory.op_le_op_iff.1 this
end PretorsionImageClosed.Statement.PretorsionTheory
