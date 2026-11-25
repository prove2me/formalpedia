-- Prove2me | solution 1 for PretorsionImageClosed.Statement.traceRejectCondition_of_quotient_reject
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:38:55.245988+00:00
-- url     : https://prove2.me/submissions/25dc93bb-910a-47ef-98b4-7f3f46a44c09

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_IsShortPreexact_of_quotient
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_arrow_comp_eq_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_isPrecokernel
public import Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_isPrekernel
public import Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_isShortPreexact
public import Theorems.Thm_PretorsionImageClosed_Subobject_preimage_factors_iff
public import Theorems.Thm_PretorsionImageClosed_Subobject_preimage_imageSubobject_arrow_comp


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {T F G : Subcategory C} (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) (hG : G.IsSubobjectClosed) (hGF : ∀ Y, G.prop Y → F.prop Y) {X : C}
    (hX : TraceRejectCondition T F X) (hV : TraceRejectCondition T G (cokernel (F.reject X).arrow)) :
    TraceRejectCondition T G X := by
  have h3 := hX.trace_cokernel
  let πA : (T.trace X : C) ⟶ (T.trace (cokernel (F.reject X).arrow) : C) :=
    factorThruImageSubobject ((T.trace X).arrow ≫ cokernel.π (F.reject X).arrow) ≫
      (Subobject.isoOfEq' h3.symm).hom
  haveI : Epi πA := epi_comp _ _
  have hcomm : πA ≫ (T.trace (cokernel (F.reject X).arrow)).arrow =
      (T.trace X).arrow ≫ cokernel.π (F.reject X).arrow := by
    simp only [πA, Category.assoc, Subobject.isoOfEq'_hom_arrow, imageSubobject_arrow_comp]
  clear_value πA
  have hs : IsShortPreexact (T.prop ⊓ G.prop) (T.trace (cokernel (F.reject X).arrow)).arrow
      (cokernel.π (G.reject (cokernel (F.reject X).arrow)).arrow) :=
    ⟨hV.isPrekernel hT hG, hV.isPrecokernel hT hG⟩
  have hpull : ∀ {Y : C} (u' : Y ⟶ X) (w : Y ⟶ (T.trace (cokernel (F.reject X).arrow) : C)),
      w ≫ (T.trace (cokernel (F.reject X).arrow)).arrow = u' ≫ cokernel.π (F.reject X).arrow →
        ∃ w' : Y ⟶ (T.trace X : C), w' ≫ (T.trace X).arrow = u' := by
    intro Y u' w hw
    have hfac : (Subobject.preimage (cokernel.π (F.reject X).arrow)
        (T.trace (cokernel (F.reject X).arrow))).Factors u' :=
      (Subobject.preimage_factors_iff _ _ _).2 ((Subobject.factors_iff _ _).2 ⟨w, hw⟩)
    rw [h3, Subobject.preimage_imageSubobject_arrow_comp _ _
      (by rw [kernelSubobject_cokernel_π_arrow]; exact hX.reject_le_trace)] at hfac
    exact ⟨_, Subobject.factorThru_arrow _ _ hfac⟩
  have hK : ∀ {W : C} (g : (T.trace X : C) ⟶ W), (T.prop ⊓ G.prop) W → kernel.ι πA ≫ g = 0 := by
    intro W g hW
    have h0 : (kernel.ι πA ≫ (T.trace X).arrow) ≫ cokernel.π (F.reject X).arrow = 0 := by
      rw [Category.assoc, ← hcomm, ← Category.assoc, kernel.condition, zero_comp]
    have hfr : (F.reject X).Factors (kernel.ι πA ≫ (T.trace X).arrow) := by
      have := kernelSubobject_factors (cokernel.π (F.reject X).arrow) _ h0
      rwa [kernelSubobject_cokernel_π_arrow] at this
    have hc : kernel.ι πA =
        (F.reject X).factorThru _ hfr ≫ Subobject.ofLE _ _ hX.reject_le_trace := by
      rw [← cancel_mono (T.trace X).arrow, Category.assoc, Subobject.ofLE_arrow,
        Subobject.factorThru_arrow]
    have hmk : (Subobject.mk (Subobject.ofLE (F.reject X) (T.trace X) hX.reject_le_trace)).arrow ≫
        g = 0 := by
      rw [← hX.reject_trace]
      exact reject_arrow_comp_eq_zero hF g (hGF W hW.2)
    rw [hc, Category.assoc, ← Subobject.underlyingIso_arrow
      (Subobject.ofLE (F.reject X) (T.trace X) hX.reject_le_trace), Category.assoc, hmk,
      comp_zero, comp_zero]
  have hseq := IsShortPreexact.of_quotient (cokernel.π (F.reject X).arrow) (T.trace X).arrow πA
    (T.trace (cokernel (F.reject X).arrow)).arrow
    (cokernel.π (G.reject (cokernel (F.reject X).arrow)).arrow) hs hcomm hpull hK
  exact traceRejectCondition_of_isShortPreexact hT hG (T.prop_trace X)
    (G.prop_cokernel_reject _) hseq
end PretorsionImageClosed.Statement
