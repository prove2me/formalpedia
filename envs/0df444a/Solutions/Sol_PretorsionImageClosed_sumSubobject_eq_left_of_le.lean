-- Prove2me | solution 1 for PretorsionImageClosed.sumSubobject_eq_left_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:16:38.810714+00:00
-- url     : https://prove2.me/submissions/ba8cfd80-6810-4323-bfa1-c66e1b27cd94

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
theorem _root_.solution {X : C} {S S' : Subobject X} (h : S' ≤ S) :
    sumSubobject S S' = S := by
  apply le_antisymm
  · exact imageSubobject_le _ (biprod.desc (𝟙 _) (Subobject.ofLE S' S h)) (by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, Category.id_comp, biprod.inl_desc]
      · rw [biprod.inr_desc_assoc, Subobject.ofLE_arrow, biprod.inr_desc])
  · exact le_sumSubobject_left S S'
end PretorsionImageClosed
