-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.op_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:47:58.476726+00:00
-- url     : https://prove2.me/submissions/0c2ae362-6192-40ed-899c-a4b6184d8612

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
theorem _root_.solution (P : PretorsionTheory C) : P.op.middle = P.middle.op := by
  unfold PretorsionTheory.middle PretorsionTheory.op
  rw [ObjectProperty.op_inf, inf_comm]
  rfl
end PretorsionImageClosed.Statement.PretorsionTheory
