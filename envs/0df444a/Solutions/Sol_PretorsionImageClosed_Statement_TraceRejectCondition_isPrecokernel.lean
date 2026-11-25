-- Prove2me | solution 1 for PretorsionImageClosed.Statement.TraceRejectCondition.isPrecokernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:52.948579+00:00
-- url     : https://prove2.me/submissions/2f2cdfd2-340c-4bbf-a785-97ce22101fa5

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_P2M_PretorsionImageClosed_Statement_TraceRejectCondition_isTrivial_arrow_comp___baf7fd259ffe
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le_kernelSubobject


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
    IsPrecokernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by
  refine ⟨h.isTrivial_arrow_comp_π hT hF, fun {W} g hg => ?_⟩
  obtain ⟨N, hN, a, b, hab⟩ := hg
  have hle : F.reject (T.trace X : C) ≤ kernelSubobject a :=
    reject_le_kernelSubobject hF a hN.2
  rw [h.reject_trace, Subobject.le_kernelSubobject_iff] at hle
  have hza : Subobject.ofLE (F.reject X) (T.trace X) h.reject_le_trace ≫ a = 0 := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc] at hle
    rwa [← cancel_epi (Subobject.underlyingIso (Subobject.ofLE (F.reject X) (T.trace X)
      h.reject_le_trace)).hom, comp_zero]
  have hrg : (F.reject X).arrow ≫ g = 0 := by
    rw [← Subobject.ofLE_arrow h.reject_le_trace, Category.assoc, ← hab, ← Category.assoc, hza,
      zero_comp]
  refine ⟨cokernel.desc _ g hrg, cokernel.π_desc _ _ _, fun w hw => ?_⟩
  rw [← cancel_epi (cokernel.π (F.reject X).arrow), hw, cokernel.π_desc]
end TraceRejectCondition
end PretorsionImageClosed.Statement
