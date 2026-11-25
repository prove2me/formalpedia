-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isPretorsionTheory_top_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:30:21.931041+00:00
-- url     : https://prove2.me/submissions/3b5744b3-5eee-4919-beb7-aea3a3dd44a7

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isQuotientClosed_top
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_eq_top_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_of_realization
public import Theorems.Thm_PretorsionImageClosed_Statement_isTrivial_of_closed


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {F : Subcategory C} (hF : F.IsSubobjectClosed) :
    IsPretorsionTheory (⊤ : Subcategory C).prop F.prop := by
  refine isPretorsionTheory_of_realization isQuotientClosed_top hF (fun Y => ?_) (fun E => ?_)
  · have ht : (⊤ : Subcategory C).trace Y = ⊤ := (trace_eq_top_iff isQuotientClosed_top).2 trivial
    haveI : IsIso ((⊤ : Subcategory C).trace Y).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ht
    exact ⟨fun h => ⟨trivial, F.prop_of_iso (asIso ((⊤ : Subcategory C).trace Y).arrow).symm h⟩,
      fun h => F.prop_of_iso (asIso ((⊤ : Subcategory C).trace Y).arrow) h.2⟩
  · exact ⟨fun _ {Y} f hY => isTrivial_of_closed isQuotientClosed_top hF f trivial hY, fun _ => trivial⟩
end PretorsionImageClosed.Statement
