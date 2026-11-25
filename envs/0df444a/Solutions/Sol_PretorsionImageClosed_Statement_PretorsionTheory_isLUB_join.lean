-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.isLUB_join
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:40:59.963486+00:00
-- url     : https://prove2.me/submissions/6133cf9e-fe85-4109-9226-08c909f8bbf2

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_le_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_LE_op_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_unop
attribute [local simp] PretorsionImageClosed.Statement.PretorsionTheory.op_unop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_unop



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
theorem _root_.solution (S : Set (PretorsionTheory C)) : IsLUB S (join S) := by
  refine ⟨fun P hP => ?_, fun Q hQ => ?_⟩
  · rw [le_iff, ← op_LE_op_iff, join, op_unop]
    exact (isGLB_meet _).1 ⟨P, hP, rfl⟩
  · rw [le_iff, ← op_LE_op_iff, join, op_unop]
    refine (isGLB_meet _).2 ?_
    rintro _ ⟨P, hP, rfl⟩
    exact op_LE_op_iff.2 (hQ hP)
end PretorsionImageClosed.Statement.PretorsionTheory
