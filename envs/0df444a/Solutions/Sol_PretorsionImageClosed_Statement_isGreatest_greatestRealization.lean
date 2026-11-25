-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isGreatest_greatestRealization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:55:59.566262+00:00
-- url     : https://prove2.me/submissions/c3b2cfb5-1a00-485a-a34e-2ba8c242cef6

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Theorems.Thm_PretorsionImageClosed_Statement_realization_bounds
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
variable {Z}
namespace PretorsionImageClosed.Statement
theorem _root_.solution :
    IsGreatest {P : PretorsionTheory C | P.middle = Z.prop} (greatestRealization Z hZ) :=
  ⟨greatestRealization_middle Z hZ, fun P hP => (realization_bounds hZ P hP).2⟩
end PretorsionImageClosed.Statement
