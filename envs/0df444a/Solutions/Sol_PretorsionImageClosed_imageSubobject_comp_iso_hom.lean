-- Prove2me | solution 1 for PretorsionImageClosed.imageSubobject_comp_iso_hom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:58.778824+00:00
-- url     : https://prove2.me/submissions/cc6af352-727b-44a2-8d33-b815da58b5b9

module
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
theorem _root_.solution {X Y Y' : C} (f : X ⟶ Y) (e : Y ≅ Y') :
    imageSubobject (f ≫ e.hom) = Subobject.mk ((imageSubobject f).arrow ≫ e.hom) := by
  conv_lhs => rw [← Subobject.mk_arrow (imageSubobject (f ≫ e.hom))]
  apply Subobject.mk_eq_mk_of_comm _ _ (imageSubobjectCompIso f e.hom)
  rw [← Category.assoc, imageSubobjectCompIso_hom_arrow, Category.assoc, IsIso.Iso.inv_hom,
    Iso.inv_hom_id, Category.comp_id]
end PretorsionImageClosed
