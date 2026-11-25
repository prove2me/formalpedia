-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.meetT_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:46:35.919936+00:00
-- url     : https://prove2.me/submissions/6e3feef8-570a-4e9e-8133-217b5f1679a3

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
namespace PretorsionImageClosed.Statement.PretorsionTheory
theorem _root_.solution {P : PretorsionTheory C} (hP : P ∈ S) : (meetT S).prop ≤ P.T.prop :=
  fun X hX => (iInf_prop_iff _ X).1 hX ⟨P, hP⟩
end PretorsionImageClosed.Statement.PretorsionTheory
