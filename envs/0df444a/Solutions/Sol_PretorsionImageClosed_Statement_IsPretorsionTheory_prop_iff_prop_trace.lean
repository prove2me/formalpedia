-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPretorsionTheory.prop_iff_prop_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:15.663222+00:00
-- url     : https://prove2.me/submissions/18f75d82-1ce5-40cf-a3c9-711a02aef9d2

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_traceRejectCondition
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_eq_bot_iff


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
variable (hP : IsPretorsionTheory T.prop F.prop)
include hP
namespace PretorsionImageClosed.Statement
namespace IsPretorsionTheory
theorem _root_.solution (Y : C) :
    F.prop Y ↔ (T.prop ⊓ F.prop) (T.trace Y : C) := by
  have hF : F.IsSubobjectClosed := hP.isSubobjectClosed
  have hc := hP.traceRejectCondition Y
  constructor
  · intro hY
    refine ⟨T.prop_trace Y, ?_⟩
    rw [← reject_eq_bot_iff hF, hc.reject_trace, Subobject.mk_eq_bot_iff_zero,
      ← cancel_mono (T.trace Y).arrow, Subobject.ofLE_arrow, zero_comp]
    have hr : F.reject Y = ⊥ := (reject_eq_bot_iff hF).2 hY
    rw [hr, Subobject.bot_arrow]
  · intro hZ
    have hr : F.reject (T.trace Y : C) = ⊥ := (reject_eq_bot_iff hF).2 hZ.2
    rw [hc.reject_trace, Subobject.mk_eq_bot_iff_zero] at hr
    rw [← reject_eq_bot_iff hF, ← Subobject.mk_arrow (F.reject Y), Subobject.mk_eq_bot_iff_zero,
      ← Subobject.ofLE_arrow hc.reject_le_trace, hr, zero_comp]
end IsPretorsionTheory
end PretorsionImageClosed.Statement
