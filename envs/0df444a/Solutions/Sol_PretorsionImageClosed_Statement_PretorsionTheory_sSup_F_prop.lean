-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.sSup_F_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:35.623891+00:00
-- url     : https://prove2.me/submissions/3ebc7bb4-8634-46e3-bf0d-1f5c59bc570e

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_eq_join
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_join_F
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meetT_op_image
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_prop
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
theorem _root_.solution (S : Set (PretorsionTheory C)) : (sSup S).F.prop = ⨅ P ∈ S, P.F.prop := by
  rw [sSup_eq_join, join_F, Subcategory.unop_prop, meetT_op_image]
  rfl
end PretorsionImageClosed.Statement.PretorsionTheory
