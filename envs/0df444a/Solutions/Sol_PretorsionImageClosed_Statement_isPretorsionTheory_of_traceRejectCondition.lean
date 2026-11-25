-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isPretorsionTheory_of_traceRejectCondition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:17.887729+00:00
-- url     : https://prove2.me/submissions/20341a2a-1a26-435e-8f94-18e4249971f5

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_isPrekernel
public import Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_isPrecokernel
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
namespace PretorsionImageClosed.Statement
theorem _root_.solution (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) (h : ∀ X, TraceRejectCondition T F X) :
    IsPretorsionTheory T.prop F.prop := by
  refine ⟨fun {X Y} f hX hY => ?_, fun X => ⟨_, _, (T.trace X).arrow,
    (cokernel.π (F.reject X).arrow), T.prop_trace X, F.prop_cokernel_reject X,
    (h X).isPrekernel hT hF, (h X).isPrecokernel hT hF⟩⟩
  exact ⟨image f, ⟨hT (factorThruImage f) inferInstance hX, hF (image.ι f) inferInstance hY⟩,
    factorThruImage f, image.ι f, image.fac f⟩
end PretorsionImageClosed.Statement
