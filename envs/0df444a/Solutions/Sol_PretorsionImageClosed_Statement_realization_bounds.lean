-- Prove2me | solution 1 for PretorsionImageClosed.Statement.realization_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:48:46.53937+00:00
-- url     : https://prove2.me/submissions/1d476f47-dcf5-4007-adf2-a0e625bfb34b

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_LE_op_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_unop
public import Theorems.Thm_PretorsionImageClosed_Statement_le_greatestRealization
attribute [local simp] PretorsionImageClosed.Statement.PretorsionTheory.op_unop
attribute [local simp] PretorsionImageClosed.Statement.Subcategory.op_unop



set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
variable {Z}
namespace PretorsionImageClosed.Statement
theorem _root_.solution (P : PretorsionTheory C) (hP : P.middle = Z.prop) :
    leastRealization Z hZ ≤ P ∧ P ≤ greatestRealization Z hZ := by
  refine ⟨?_, le_greatestRealization hZ P hP⟩
  have hP' : P.op.middle = Z.op.prop := by
    rw [PretorsionTheory.op_middle, hP]
    rfl
  have h := le_greatestRealization hZ.op P.op hP'
  rw [← PretorsionTheory.op_unop (greatestRealization Z.op hZ.op)] at h
  exact PretorsionTheory.op_LE_op_iff.1 h
end PretorsionImageClosed.Statement
