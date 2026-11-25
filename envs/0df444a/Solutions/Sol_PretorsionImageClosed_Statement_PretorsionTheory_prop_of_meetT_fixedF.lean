-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.prop_of_meetT_fixedF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:47:33.138097+00:00
-- url     : https://prove2.me/submissions/ce0e2f6a-f3c8-4ec3-ad8c-905ad75d3a94

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_eq_top_iff


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory
variable (S : Set (PretorsionTheory C)) (Z : Subcategory C)
variable {S Z} {P₀ : PretorsionTheory C} (hP₀ : P₀ ∈ S) (hS : ∀ P ∈ S, P.middle = Z.prop)
include hP₀ hS
omit hP₀ hS
namespace PretorsionImageClosed.Statement.PretorsionTheory
theorem _root_.solution {X : C} (hX : (meetT S).prop X) (hF : (fixedF S Z).prop X) :
    Z.prop X := by
  have ht : (meetT S).trace X = ⊤ := (trace_eq_top_iff (isQuotientClosed_meetT S)).2 hX
  haveI : IsIso ((meetT S).trace X).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ht
  exact Z.prop_of_iso (asIso ((meetT S).trace X).arrow) hF
end PretorsionImageClosed.Statement.PretorsionTheory
