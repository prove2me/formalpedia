-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.isSubobjectClosed_fixedF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:51:37.730669+00:00
-- url     : https://prove2.me/submissions/388927ea-b8fd-4db5-ad4a-7d887450f791

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_prop_of_mono_of_meetT

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
namespace PretorsionImageClosed.Statement.PretorsionTheory
theorem _root_.solution : (fixedF S Z).IsSubobjectClosed := by
  intro X Y f hf hY
  haveI := hf
  haveI : Mono (traceMap (isQuotientClosed_meetT S) f) :=
    mono_of_mono_fac (traceMap_arrow (isQuotientClosed_meetT S) f)
  exact prop_of_mono_of_meetT hP₀ hS (traceMap (isQuotientClosed_meetT S) f)
    ((meetT S).prop_trace X) hY
end PretorsionImageClosed.Statement.PretorsionTheory
