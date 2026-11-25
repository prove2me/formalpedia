-- Prove2me | solution 1 for PretorsionImageClosed.Statement.kernelSubobject_eq_reject_of_isPrecokernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:30:19.71232+00:00
-- url     : https://prove2.me/submissions/24d8f7e9-814f-42d4-8ad4-ff36b2dfd0ad

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_isTrivial_of_closed
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_reject_iff
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
variable (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
include hT hF
namespace PretorsionImageClosed.Statement
theorem _root_.solution {T' F' : C} {u : T' ⟶ X} {v : X ⟶ F'}
    (hT' : T.prop T') (hF' : F.prop F') (hv : IsPrecokernel (T.prop ⊓ F.prop) u v) :
    kernelSubobject v = F.reject X := by
  apply le_antisymm
  · rw [le_reject_iff hF]
    intro Y g hY
    obtain ⟨w, hw, -⟩ := hv.2 g (isTrivial_of_closed hT hF (u ≫ g) hT' hY)
    rw [← hw, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
  · exact reject_le_kernelSubobject hF v hF'
end PretorsionImageClosed.Statement
