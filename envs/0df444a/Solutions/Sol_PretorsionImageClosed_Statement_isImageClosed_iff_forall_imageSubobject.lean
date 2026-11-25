-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isImageClosed_iff_forall_imageSubobject
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:15:55.413584+00:00
-- url     : https://prove2.me/submissions/ccf1214d-9be0-48b4-8e80-adb8c810cc49

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA

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
namespace PretorsionImageClosed.Statement
theorem _root_.solution (Z : Subcategory C) :
    Z.IsImageClosed ↔ ∀ {X N : C} (f : X ⟶ N), Z.prop X → Z.prop N → Z.prop (imageSubobject f : C) :=
  ⟨fun hZ _ _ f hX hN => hZ.prop_imageSubobject f hX hN,
   fun h _ _ f hX hN => Z.prop_of_iso (imageSubobjectIso f) (h f hX hN)⟩
end PretorsionImageClosed.Statement
