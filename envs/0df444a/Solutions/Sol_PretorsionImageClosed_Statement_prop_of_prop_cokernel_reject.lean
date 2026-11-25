-- Prove2me | solution 1 for PretorsionImageClosed.Statement.prop_of_prop_cokernel_reject
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:44.588438+00:00
-- url     : https://prove2.me/submissions/98f8a52b-afd4-4463-81e9-c8c35a5f6987

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_prop_iff_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_reject_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_arrow_comp_eq_zero


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {T F G : Subcategory C} (hP : IsPretorsionTheory T.prop F.prop)
    (hG : G.IsSubobjectClosed) (hFG : ∀ Y, F.prop Y → G.prop Y) {X : C}
    (hX : T.prop (cokernel (G.reject X).arrow)) : T.prop X := by
  have hF : F.IsSubobjectClosed := hP.isSubobjectClosed
  have hle : G.reject X ≤ F.reject X := by
    rw [le_reject_iff hF]
    intro Y g hY
    exact reject_arrow_comp_eq_zero hG g (hFG Y hY)
  have hz : (G.reject X).arrow ≫ cokernel.π (F.reject X).arrow = 0 := by
    rw [← Subobject.ofLE_arrow hle, Category.assoc, cokernel.condition, comp_zero]
  have hfac : cokernel.π (G.reject X).arrow ≫ cokernel.desc _ _ hz = cokernel.π (F.reject X).arrow :=
    cokernel.π_desc _ _ _
  haveI : Epi (cokernel.desc _ _ hz) := epi_of_epi_fac hfac
  exact (hP.prop_iff_prop_cokernel_reject X).2
    ⟨hP.isQuotientClosed (cokernel.desc _ _ hz) inferInstance hX, F.prop_cokernel_reject X⟩
end PretorsionImageClosed.Statement
