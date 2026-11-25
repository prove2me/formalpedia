-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isSubobjectClosed_finInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:54:20.789715+00:00
-- url     : https://prove2.me/submissions/fd2265c9-ca18-4865-af9a-2b8593d66402

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable {ι : Type*} (F : ι → Subcategory C)
variable {F} {T : Subcategory C} (hT : T.IsQuotientClosed) (h : ∀ i, IsPretorsionTheory T.prop (F i).prop)
include hT h
omit hT
namespace PretorsionImageClosed.Statement
theorem _root_.solution (J : Finset ι) : (finInf F J).IsSubobjectClosed :=
  IsSubobjectClosed.iInf fun i => (h i.1).isSubobjectClosed
end PretorsionImageClosed.Statement
