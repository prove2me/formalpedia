-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPretorsionTheory.traceRejectCondition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:38:53.637819+00:00
-- url     : https://prove2.me/submissions/221a5a8e-2371-4883-9ac0-4652db96a93b

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_isShortPreexact
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed


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
namespace IsPretorsionTheory
theorem _root_.solution (hP : IsPretorsionTheory T.prop F.prop) (X : C) :
    TraceRejectCondition T F X := by
  obtain ⟨T', F', u, v, hT', hF', hs⟩ := hP.2 X
  exact traceRejectCondition_of_isShortPreexact hP.isQuotientClosed hP.isSubobjectClosed hT' hF' hs
end IsPretorsionTheory
end PretorsionImageClosed.Statement
