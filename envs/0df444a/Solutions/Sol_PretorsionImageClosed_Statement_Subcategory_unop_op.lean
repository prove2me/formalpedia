-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.unop_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:05:06.021066+00:00
-- url     : https://prove2.me/submissions/3604ea37-4ded-417c-8159-a4e828194412

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext

attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_prop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.unop_prop

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
namespace Subcategory
theorem _root_.solution (Z : Subcategory C) : Z.op.unop = Z := Subcategory.ext rfl
end Subcategory
end PretorsionImageClosed.Statement
