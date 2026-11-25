-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.isTorsion_iff_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:53:36.028944+00:00
-- url     : https://prove2.me/submissions/be6d1826-2fda-4d05-92d3-07f8b9b7f44e

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
public import Theorems.Thm_PretorsionImageClosed_Statement_isTorsionPair_iff

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory ZeroObject
variable {C : Type*} [Category C] [Abelian C]
variable [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory
namespace PretorsionImageClosed.Statement.PretorsionTheory
theorem _root_.solution (P : PretorsionTheory C) :
    P.IsTorsion ↔ P.middle = (⊥ : Subcategory C).prop := by
  rw [IsTorsion, isTorsionPair_iff]
  refine ⟨fun h => ?_, fun h => ⟨P.isPretorsionTheory, fun X hX => ?_⟩⟩
  · funext X
    apply propext
    exact ⟨h.2 X, fun hX => ⟨P.T.prop_of_isZero hX, P.F.prop_of_isZero hX⟩⟩
  · have : P.middle X := hX
    rw [h] at this
    exact this
end PretorsionImageClosed.Statement.PretorsionTheory
