-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.isTorsion_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:55:17.379451+00:00
-- url     : https://prove2.me/submissions/1c1f4552-1d80-40c9-946a-41bb273b6993

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isTorsion_iff_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_bot_eq


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
theorem _root_.solution : (⊥ : PretorsionTheory C).IsTorsion := by
  rw [isTorsion_iff_middle, bot_eq]
  funext X
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
end PretorsionImageClosed.Statement.PretorsionTheory
