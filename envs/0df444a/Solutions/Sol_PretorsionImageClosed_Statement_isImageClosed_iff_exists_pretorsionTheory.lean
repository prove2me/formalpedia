-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isImageClosed_iff_exists_pretorsionTheory
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:16:07.627753+00:00
-- url     : https://prove2.me/submissions/61ccd486-9611-483c-b415-3d1ebb1a6ad9

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Theorems.Thm_PretorsionImageClosed_Statement_greatestRealization_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isImageClosed_middle

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
theorem _root_.solution (Z : Subcategory C) :
    Z.IsImageClosed ↔ ∃ P : PretorsionTheory C, P.middle = Z.prop := by
  constructor
  · intro hZ
    exact ⟨greatestRealization Z hZ, greatestRealization_middle Z hZ⟩
  · rintro ⟨P, hP⟩
    have : (P.T ⊓ P.F).IsImageClosed := P.isImageClosed_middle
    change Statement.IsImageClosed (P.T.prop ⊓ P.F.prop) at this
    rwa [show P.T.prop ⊓ P.F.prop = Z.prop from hP] at this
end PretorsionImageClosed.Statement
