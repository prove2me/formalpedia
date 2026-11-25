-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isLeast_leastRealization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:55:58.716473+00:00
-- url     : https://prove2.me/submissions/076493d8-6cf4-4f78-ae64-2942580cf99e

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Theorems.Thm_PretorsionImageClosed_Statement_leastRealization_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_realization_bounds

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
    IsLeast {P : PretorsionTheory C | P.middle = Z.prop} (leastRealization Z hZ) :=
  ⟨leastRealization_middle Z hZ, fun P hP => (realization_bounds hZ P hP).1⟩
end PretorsionImageClosed.Statement
