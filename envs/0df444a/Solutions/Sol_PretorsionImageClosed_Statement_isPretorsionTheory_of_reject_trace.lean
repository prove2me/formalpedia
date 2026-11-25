-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isPretorsionTheory_of_reject_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:30:23.830821+00:00
-- url     : https://prove2.me/submissions/1ee4ef63-d564-4bdf-8097-9aa88886958b

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_eq_bot_iff
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
theorem _root_.solution {T F : Subcategory C} (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed)
    (hrt : ∀ X : C, ∃ h : F.reject X ≤ T.trace X,
      F.reject (T.trace X : C) = Subobject.mk (Subobject.ofLE _ _ h))
    (hTZ : ∀ X : C, T.prop X ↔ (T.prop ⊓ F.prop) (cokernel (F.reject X).arrow)) :
    IsPretorsionTheory T.prop F.prop := by
  refine isPretorsionTheory_of_realization hT hF (fun Y => ?_) (fun E => ?_)
  · refine ⟨fun hY => ⟨T.prop_trace Y, hF (T.trace Y).arrow inferInstance hY⟩, fun hZ => ?_⟩
    obtain ⟨hle, heq⟩ := hrt Y
    have hr : F.reject (T.trace Y : C) = ⊥ := (reject_eq_bot_iff hF).2 hZ.2
    rw [heq, Subobject.mk_eq_bot_iff_zero] at hr
    rw [← reject_eq_bot_iff hF, ← Subobject.mk_arrow (F.reject Y), Subobject.mk_eq_bot_iff_zero,
      ← Subobject.ofLE_arrow hle, hr, zero_comp]
  · refine ⟨fun hE {Y} f hY => isTrivial_of_closed hT hF f hE hY, fun h => ?_⟩
    obtain ⟨W, hW, g, k, hgk⟩ := h (cokernel.π (F.reject E).arrow) (F.prop_cokernel_reject E)
    haveI : Epi k := epi_of_epi_fac hgk
    exact (hTZ E).2 ⟨hT k inferInstance hW.1, F.prop_cokernel_reject E⟩
end PretorsionImageClosed.Statement
