-- Prove2me | solution 1 for PretorsionImageClosed.Statement.TraceRejectCondition.isPrekernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:38.671858+00:00
-- url     : https://prove2.me/submissions/4bcb97f9-0c39-400d-a4c5-0a2b8dc78bb4

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_P2M_PretorsionImageClosed_Statement_TraceRejectCondition_isTrivial_arrow_comp___baf7fd259ffe
public import Theorems.Thm_PretorsionImageClosed_Subobject_preimage_factors_iff
public import Theorems.Thm_PretorsionImageClosed_Subobject_preimage_imageSubobject_arrow_comp


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
variable (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed) (h : TraceRejectCondition T F X)
include hT hF h
namespace PretorsionImageClosed.Statement
namespace TraceRejectCondition
theorem _root_.solution :
    IsPrekernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by
  refine ⟨h.isTrivial_arrow_comp_π hT hF, fun {W} f hf => ?_⟩
  obtain ⟨N, hN, a, b, hab⟩ := hf
  have hb : imageSubobject b ≤ (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))) := by
    rw [← h.trace_cokernel]
    exact le_trace hT
      (T.prop_of_iso (imageSubobjectIso b).symm (hT (factorThruImage b) inferInstance hN.1))
  have hfac : (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))).Factors (f ≫ (cokernel.π (F.reject X).arrow)) := by
    rw [← hab]
    exact Subobject.factors_of_le _ hb (imageSubobject_factors_comp_self b a)
  have hP : Subobject.preimage (cokernel.π (F.reject X).arrow) (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))) = T.trace X :=
    Subobject.preimage_imageSubobject_arrow_comp (cokernel.π (F.reject X).arrow) (T.trace X)
      (by rw [kernelSubobject_cokernel_π_arrow]; exact h.reject_le_trace)
  have hf' : (T.trace X).Factors f := hP ▸ (Subobject.preimage_factors_iff (cokernel.π (F.reject X).arrow) (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))) f).2 hfac
  refine ⟨(T.trace X).factorThru f hf', Subobject.factorThru_arrow _ _ _, fun w hw => ?_⟩
  rw [← cancel_mono (T.trace X).arrow, hw, Subobject.factorThru_arrow]
end TraceRejectCondition
end PretorsionImageClosed.Statement
