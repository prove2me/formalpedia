-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.isImageClosed_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:14:00.590277+00:00
-- url     : https://prove2.me/submissions/202a7666-777d-4bf8-91a2-e3eba9451137

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_inf_of_closed


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
variable {Z hZ}
namespace PretorsionImageClosed.Statement
namespace PretorsionTheory
theorem _root_.solution (P : PretorsionTheory C) :
    (P.T ⊓ P.F).IsImageClosed :=
  IsImageClosed.inf_of_closed P.isPretorsionTheory.isQuotientClosed
    P.isPretorsionTheory.isSubobjectClosed
end PretorsionTheory
end PretorsionImageClosed.Statement
