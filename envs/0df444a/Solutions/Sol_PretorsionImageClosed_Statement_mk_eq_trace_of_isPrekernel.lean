-- Prove2me | solution 1 for PretorsionImageClosed.Statement.mk_eq_trace_of_isPrekernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:30:16.88606+00:00
-- url     : https://prove2.me/submissions/dca97e99-81d2-47ae-a887-3d2636128261

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_isTrivial_of_closed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono


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
theorem _root_.solution {T' F' : C} {u : T' ⟶ X} {v : X ⟶ F'} (hT' : T.prop T')
    (hF' : F.prop F') (hu : IsPrekernel (T.prop ⊓ F.prop) u v) :
    haveI := hu.mono
    Subobject.mk u = T.trace X := by
  haveI := hu.mono
  apply le_antisymm
  · exact le_trace hT (T.prop_of_iso (Subobject.underlyingIso u).symm hT')
  · obtain ⟨w, hw, -⟩ := hu.2 (T.trace X).arrow (isTrivial_of_closed hT hF _ (T.prop_trace X) hF')
    exact Subobject.le_mk_of_comm w hw
end PretorsionImageClosed.Statement
