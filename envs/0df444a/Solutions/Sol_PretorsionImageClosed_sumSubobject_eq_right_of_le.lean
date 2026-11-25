-- Prove2me | solution 1 for PretorsionImageClosed.sumSubobject_eq_right_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:16:28.078416+00:00
-- url     : https://prove2.me/submissions/418ab949-7819-41d3-9316-0cc51e2e954b

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
theorem _root_.solution {X : C} {S S' : Subobject X} (h : S ≤ S') :
    sumSubobject S S' = S' := by
  apply le_antisymm
  · exact imageSubobject_le _ (biprod.desc (Subobject.ofLE S S' h) (𝟙 _)) (by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, Subobject.ofLE_arrow, biprod.inl_desc]
      · rw [biprod.inr_desc_assoc, Category.id_comp, biprod.inr_desc])
  · exact le_sumSubobject_right S S'
end PretorsionImageClosed
