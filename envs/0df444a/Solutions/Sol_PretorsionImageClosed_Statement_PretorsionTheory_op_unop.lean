-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.op_unop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:19:26.740469+00:00
-- url     : https://prove2.me/submissions/d68935f4-b5fe-44f7-adfc-f803cfaee999

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_op
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_unop_op
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext

attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_prop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.unop_prop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.unop_op
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_unop
attribute [local simp] PretorsionImageClosed.Statement.PretorsionTheory.unop_op

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Opposite
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed.Statement
namespace PretorsionTheory
theorem _root_.solution (P : PretorsionTheory Cᵒᵖ) : P.unop.op = P :=
  PretorsionTheory.ext (Subcategory.op_unop _) (Subcategory.op_unop _)
end PretorsionTheory
end PretorsionImageClosed.Statement
