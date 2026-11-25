-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.op_LE_op_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:07:33.676431+00:00
-- url     : https://prove2.me/submissions/cdc5ee96-dc9a-41a4-9678-cf505d8ab583

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_le_op_iff

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
theorem _root_.solution {P Q : PretorsionTheory C} : P.op.LE Q.op ↔ Q.LE P := by
  unfold PretorsionTheory.LE PretorsionTheory.op
  exact ⟨fun h => ⟨Subcategory.op_le_op_iff.1 h.2, Subcategory.op_le_op_iff.1 h.1⟩,
    fun h => ⟨Subcategory.op_le_op_iff.2 h.2, Subcategory.op_le_op_iff.2 h.1⟩⟩
end PretorsionTheory
end PretorsionImageClosed.Statement
