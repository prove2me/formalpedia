-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.unop_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:48:06.128938+00:00
-- url     : https://prove2.me/submissions/16415ede-d241-41fa-bb3f-b0fefdce3957

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle

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
theorem _root_.solution (P : PretorsionTheory Cᵒᵖ) : P.unop.middle = P.middle.unop := by
  unfold PretorsionTheory.middle PretorsionTheory.unop
  rw [ObjectProperty.unop_inf, inf_comm]
  rfl
end PretorsionImageClosed.Statement.PretorsionTheory
