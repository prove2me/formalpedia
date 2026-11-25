-- Prove2me | solution 1 for PretorsionImageClosed.imageSubobject_biprod_desc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:17:57.327836+00:00
-- url     : https://prove2.me/submissions/46bb4dbf-84e2-4254-98cc-4f1defbbaad8

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Theorems.Thm_PretorsionImageClosed_imageSubobject_epi_comp


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
theorem _root_.solution {Y₁ Y₂ X : C} (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) :
    imageSubobject (biprod.desc f g) = sumSubobject (imageSubobject f) (imageSubobject g) := by
  have hfac : biprod.desc f g = biprod.map (factorThruImageSubobject f) (factorThruImageSubobject g) ≫
      biprod.desc (imageSubobject f).arrow (imageSubobject g).arrow := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc, imageSubobject_arrow_comp]
    · simp only [biprod.inr_map_assoc, biprod.inr_desc, imageSubobject_arrow_comp]
  rw [hfac, imageSubobject_epi_comp]
  rfl
end PretorsionImageClosed
