-- Prove2me | solution 1 for PretorsionImageClosed.Statement.leastRealization_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:52:52.387239+00:00
-- url     : https://prove2.me/submissions/28899caf-1cca-4bc1-932e-1cc18fbf0663

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_unop_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_greatestRealization_middle


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
namespace PretorsionImageClosed.Statement
theorem _root_.solution : (leastRealization Z hZ).middle = Z.prop := by
  show (greatestRealization Z.op hZ.op).unop.middle = Z.prop
  rw [PretorsionTheory.unop_middle, greatestRealization_middle]
  rfl
end PretorsionImageClosed.Statement
