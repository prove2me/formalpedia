-- Prove2me | solution 1 for PretorsionImageClosed.Statement.traceRejectCondition_of_isShortPreexact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:35:51.39108+00:00
-- url     : https://prove2.me/submissions/973599da-3c7c-4285-8196-d0551280e8d6

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_mk_eq_trace_of_isPrekernel
public import Theorems.Thm_PretorsionImageClosed_Statement_kernelSubobject_eq_reject_of_isPrecokernel
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrecokernel_comp_iso_right
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrecokernel_epi
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrecokernel_of_iso_left
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_comp_iso_right
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_of_iso_left
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_reject_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_arrow_comp_eq_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le
public import Theorems.Thm_PretorsionImageClosed_Subobject_kernelSubobject_le_preimage
public import Theorems.Thm_PretorsionImageClosed_imageSubobject_arrow_comp_le_of_le


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
variable (T F : Subcategory C) (X : C)
variable {T F X}
variable (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
include hT hF
namespace PretorsionImageClosed.Statement
theorem _root_.solution {T' F' : C} {u : T' ⟶ X} {v : X ⟶ F'}
    (hT' : T.prop T') (hF' : F.prop F') (hs : IsShortPreexact (T.prop ⊓ F.prop) u v) :
    TraceRejectCondition T F X := by
  obtain ⟨hu, hv⟩ := hs
  haveI := hu.mono
  haveI := hv.epi
  have hmk : Subobject.mk u = T.trace X := mk_eq_trace_of_isPrekernel hT hF hT' hF' hu
  have hker : kernelSubobject v = F.reject X := kernelSubobject_eq_reject_of_isPrecokernel hT hF hT' hF' hv
  -- replace `u` by the inclusion of the trace
  have hu' : IsPrekernel (T.prop ⊓ F.prop) (T.trace X).arrow v := by
    rw [← hmk, ← Subobject.underlyingIso_hom_comp_eq_mk]
    exact hu.of_iso_left _
  have hv' : IsPrecokernel (T.prop ⊓ F.prop) (T.trace X).arrow v := by
    rw [← hmk, ← Subobject.underlyingIso_hom_comp_eq_mk]
    exact hv.of_iso_left _
  -- replace `v` by the projection onto `X/r(X)`
  have hrv : (F.reject X).arrow ≫ v = 0 := by
    rw [← hker, kernelSubobject_arrow_comp]
  have hexact : (ShortComplex.mk (F.reject X).arrow v hrv).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    change imageSubobject (F.reject X).arrow = kernelSubobject v
    rw [imageSubobject_mono, Subobject.mk_arrow, hker]
  haveI : Mono (cokernel.desc (F.reject X).arrow v hrv) := hexact.mono_cokernelDesc
  haveI : Epi (cokernel.desc (F.reject X).arrow v hrv) :=
    epi_of_epi_fac (cokernel.π_desc (F.reject X).arrow v hrv)
  haveI : IsIso (cokernel.desc (F.reject X).arrow v hrv) := isIso_of_mono_of_epi _
  set e : cokernel (F.reject X).arrow ≅ F' := asIso (cokernel.desc (F.reject X).arrow v hrv)
  have hpe : (cokernel.π (F.reject X).arrow) ≫ e.hom = v := cokernel.π_desc _ _ _
  have hu'' : IsPrekernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by
    have := (hu'.comp_iso_right e.symm)
    rwa [Iso.symm_hom, ← hpe, Category.assoc, e.hom_inv_id, Category.comp_id] at this
  have hv'' : IsPrecokernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by
    have := (hv'.comp_iso_right e.symm)
    rwa [Iso.symm_hom, ← hpe, Category.assoc, e.hom_inv_id, Category.comp_id] at this
  -- the preimage of `t(X/r(X))`
  set U := T.trace (cokernel (F.reject X).arrow)
  set P := Subobject.preimage (cokernel.π (F.reject X).arrow) U
  have hUZ : (T.prop ⊓ F.prop) (U : C) :=
    ⟨T.prop_trace _, hF U.arrow inferInstance (F.prop_cokernel_reject X)⟩
  have hPt : P ≤ T.trace X := by
    have htriv : IsTrivial (T.prop ⊓ F.prop) (P.arrow ≫ (cokernel.π (F.reject X).arrow)) :=
      ⟨_, hUZ, U.factorThru _ (Subobject.preimage_arrow_comp_factors (cokernel.π (F.reject X).arrow) U), U.arrow,
        Subobject.factorThru_arrow _ _ _⟩
    obtain ⟨w, hw, -⟩ := hu''.2 P.arrow htriv
    exact Subobject.le_of_comm w hw
  have hrt : F.reject X ≤ T.trace X := by
    have := Subobject.kernelSubobject_le_preimage (cokernel.π (F.reject X).arrow) U
    rw [kernelSubobject_cokernel_π_arrow] at this
    exact this.trans hPt
  refine ⟨hrt, ?_, ?_⟩
  · -- `r(t(X)) = r(X)`
    apply le_antisymm
    · apply reject_le hF
      have hz : Subobject.ofLE (F.reject X) (T.trace X) hrt ≫ (T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow) = 0 := by
        rw [← Category.assoc, Subobject.ofLE_arrow, cokernel.condition]
      have hexact' : (ShortComplex.mk (Subobject.ofLE (F.reject X) (T.trace X) hrt)
          ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) hz).Exact := by
        rw [ShortComplex.exact_iff_image_eq_kernel]
        change imageSubobject (Subobject.ofLE (F.reject X) (T.trace X) hrt) =
          kernelSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))
        rw [imageSubobject_mono]
        apply le_antisymm
        · exact le_kernelSubobject _ _
            (by rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc, hz, comp_zero])
        · have h1 : (kernelSubobject (cokernel.π (F.reject X).arrow)).Factors
              ((kernelSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))).arrow ≫ (T.trace X).arrow) :=
            kernelSubobject_factors _ _ (by rw [Category.assoc, kernelSubobject_arrow_comp])
          rw [kernelSubobject_cokernel_π_arrow] at h1
          refine Subobject.le_mk_of_comm ((F.reject X).factorThru _ h1) ?_
          rw [← cancel_mono (T.trace X).arrow, Category.assoc, Subobject.ofLE_arrow,
            Subobject.factorThru_arrow]
      have hmono : Mono (cokernel.desc (Subobject.ofLE (F.reject X) (T.trace X) hrt)
          ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) hz) :=
        hexact'.mono_cokernelDesc
      have hiso : cokernel (Subobject.mk (Subobject.ofLE (F.reject X) (T.trace X) hrt)).arrow ≅
          cokernel (Subobject.ofLE (F.reject X) (T.trace X) hrt) := by
        rw [← Subobject.underlyingIso_hom_comp_eq_mk]
        exact cokernelEpiComp _ _
      exact F.prop_of_iso hiso.symm (hF _ hmono (F.prop_cokernel_reject X))
    · rw [le_reject_iff hF]
      intro Y g hY
      have hc : IsTrivial (T.prop ⊓ F.prop) ((T.trace X).arrow ≫ (cokernel.π ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow))) :=
        ⟨cokernel (F.reject (T.trace X : C)).arrow,
          ⟨hT (cokernel.π (F.reject (T.trace X : C)).arrow) inferInstance (T.prop_trace X), F.prop_cokernel_reject _⟩,
          cokernel.π (F.reject (T.trace X : C)).arrow,
          cokernel.desc (F.reject (T.trace X : C)).arrow ((T.trace X).arrow ≫ (cokernel.π ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow)))
            (by rw [← Category.assoc, cokernel.condition]),
          cokernel.π_desc _ _ _⟩
      obtain ⟨w, hw, -⟩ := hv''.2 (cokernel.π ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow)) hc
      have hr : (F.reject X).arrow ≫ (cokernel.π ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow)) = 0 := by
        rw [← hw, ← Category.assoc, cokernel.condition, zero_comp]
      have hle : F.reject X ≤ Subobject.mk ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow) := by
        have := le_kernelSubobject _ _ hr
        rwa [← imageSubobject_eq_kernelSubobject_cokernel_π, imageSubobject_mono] at this
      have hw' : Subobject.ofLEMk (F.reject X) ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow) hle ≫ (F.reject (T.trace X : C)).arrow =
          Subobject.ofLE (F.reject X) (T.trace X) hrt := by
        rw [← cancel_mono (T.trace X).arrow, Category.assoc, Subobject.ofLEMk_comp,
          Subobject.ofLE_arrow]
      have hzero : Subobject.ofLE (F.reject X) (T.trace X) hrt ≫ g = 0 := by
        rw [← hw', Category.assoc, reject_arrow_comp_eq_zero hF g hY, comp_zero]
      rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc, hzero, comp_zero]
  · -- `t(X/r(X)) = t(X)/r(X)`
    apply le_antisymm
    · calc U ≤ imageSubobject (P.arrow ≫ (cokernel.π (F.reject X).arrow)) :=
            Subobject.le_imageSubobject_preimage_arrow_comp (cokernel.π (F.reject X).arrow) U
        _ ≤ imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) := imageSubobject_arrow_comp_le_of_le hPt (cokernel.π (F.reject X).arrow)
    · exact le_trace hT (T.prop_of_iso (imageSubobjectIso _).symm
        (hT (factorThruImage _) inferInstance (T.prop_trace X)))
end PretorsionImageClosed.Statement
