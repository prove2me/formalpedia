-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isPretorsionTheory_iff_traceRejectCondition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:18.748889+00:00
-- url     : https://prove2.me/submissions/57e4a6ef-533e-4aee-b60e-ede775fcd1d1

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_of_traceRejectCondition
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_traceRejectCondition

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
namespace PretorsionImageClosed.Statement
theorem _root_.solution (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) :
    IsPretorsionTheory T.prop F.prop ↔ ∀ X, TraceRejectCondition T F X :=
  ⟨fun hP X => hP.traceRejectCondition X, isPretorsionTheory_of_traceRejectCondition hT hF⟩
end PretorsionImageClosed.Statement
