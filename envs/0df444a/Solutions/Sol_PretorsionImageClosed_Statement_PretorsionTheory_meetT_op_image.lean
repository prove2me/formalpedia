-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.meetT_op_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:42:11.338469+00:00
-- url     : https://prove2.me/submissions/ca7b11dc-9d78-4705-a8fd-904f56f3e5c7

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_unop_op
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
    (meetT (PretorsionTheory.op '' S)).prop = (⨅ P ∈ S, P.F.prop).op := by
  funext X
  apply propext
  rw [meetT, iInf_prop_iff]
  simp only [ObjectProperty.op_iff, iInf_apply, iInf_Prop_eq]
  constructor
  · intro h P hP
    exact h ⟨P.op, P, hP, rfl⟩
  · rintro h ⟨_, P, hP, rfl⟩
    exact h P hP
end PretorsionImageClosed.Statement.PretorsionTheory
