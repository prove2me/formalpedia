-- Prove2me | solution 1 for PretorsionImageClosed.theoremBImageClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:52.306617+00:00
-- url     : https://prove2.me/submissions/1dbd052e-dda6-4ff9-a213-491d1639c3a3

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Definitions.Def_PretorsionImageClosed_MainTheorems
public import Theorems.Thm_PretorsionImageClosed_gandhiImageClosed
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_isGandhiSecond_gandhiSecondOf
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
open PretorsionImageClosed
open CategoryTheory Limits Statement
universe u
namespace PretorsionImageClosed
theorem _root_.solution : Statement.TheoremBImageClosed.{u} := by
  refine ⟨⟨LinearQuiver.gandhiSecondOf, LinearQuiver.isGandhiSecond_gandhiSecondOf⟩, ?_⟩
  intro k _ n
  refine ⟨inferInstance, fun Cs hCs => ?_⟩
  have h := (gandhiImageClosed.{u}.2 k n).2 Cs hCs
  rw [← h, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro Z _
  simp [imageClosedWeight]
end PretorsionImageClosed
