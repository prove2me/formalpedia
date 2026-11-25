-- Prove2me | solution 1 for P2M_PretorsionImageClosed_Statement_TraceRejectCondition_isTrivial_arrow_comp___baf7fd259ffe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:57:05.382486+00:00
-- url     : https://prove2.me/submissions/36323a8b-8848-4dde-9711-1f67964cea81

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_prop_image

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
    IsTrivial (T.prop ⊓ F.prop) ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) :=
  ⟨_, h.prop_image hT hF, factorThruImageSubobject _, (imageSubobject _).arrow,
    imageSubobject_arrow_comp _⟩
end TraceRejectCondition
end PretorsionImageClosed.Statement
