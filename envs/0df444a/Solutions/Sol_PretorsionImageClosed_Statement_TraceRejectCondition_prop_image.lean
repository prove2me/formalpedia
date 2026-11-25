-- Prove2me | solution 1 for PretorsionImageClosed.Statement.TraceRejectCondition.prop_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:51:34.828971+00:00
-- url     : https://prove2.me/submissions/c4f6c549-3779-43f9-8a5c-ab53f998b9fd

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject


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
    (T.prop ⊓ F.prop)
      (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) : C) :=
  ⟨T.prop_of_iso (imageSubobjectIso _).symm
      (hT (factorThruImage _) inferInstance (T.prop_trace X)),
   hF (imageSubobject _).arrow inferInstance (F.prop_cokernel_reject X)⟩
end TraceRejectCondition
end PretorsionImageClosed.Statement
