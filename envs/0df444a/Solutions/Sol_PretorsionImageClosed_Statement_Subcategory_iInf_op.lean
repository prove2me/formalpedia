-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.iInf_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:57:35.304083+00:00
-- url     : https://prove2.me/submissions/aefc10ae-f3c7-432e-a4e7-c2616ea1d8fe

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
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf

attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_prop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.unop_prop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.unop_op
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_unop

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
theorem _root_.solution {ι : Sort*} (Z : ι → Subcategory C) :
    (Subcategory.iInf Z).op = Subcategory.iInf (fun i => (Z i).op) := by
  apply Subcategory.ext
  funext X
  apply propext
  simp only [Subcategory.op_prop, ObjectProperty.op_iff, Subcategory.iInf_prop_iff]
end Subcategory
end PretorsionImageClosed.Statement
