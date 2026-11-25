-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isPretorsionTheory_top_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:30:13.038031+00:00
-- url     : https://prove2.me/submissions/724a3c92-4e50-4ef1-b864-16ef23cf5e3c

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isSubobjectClosed_top
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
theorem _root_.solution {T : Subcategory C} (hT : T.IsQuotientClosed) :
    IsPretorsionTheory T.prop (⊤ : Subcategory C).prop := by
  refine isPretorsionTheory_of_realization hT isSubobjectClosed_top (fun Y => ?_) (fun E => ?_)
  · exact ⟨fun _ => ⟨T.prop_trace Y, trivial⟩, fun _ => trivial⟩
  · refine ⟨fun hE {Y} f _ => isTrivial_of_closed hT isSubobjectClosed_top f hE trivial, fun h => ?_⟩
    obtain ⟨W, hW, g, k, hgk⟩ := h (𝟙 E) trivial
    exact T.prop_of_retract ⟨g, k, hgk⟩ hW.1
end PretorsionImageClosed.Statement
