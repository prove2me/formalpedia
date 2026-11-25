-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.IsTorsion.sSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:55:12.355082+00:00
-- url     : https://prove2.me/submissions/ad87fbc5-0f3f-442e-941c-479214d5802d

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isTorsion_iff_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_middle


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
namespace IsTorsion
theorem _root_.solution {S : Set (PretorsionTheory C)} (hne : S.Nonempty)
    (h : ∀ P ∈ S, P.IsTorsion) : (sSup S).IsTorsion := by
  obtain ⟨P₀, hP₀⟩ := hne
  rw [isTorsion_iff_middle]
  exact sSup_middle hP₀ fun P hP => (isTorsion_iff_middle P).1 (h P hP)
end IsTorsion
end PretorsionImageClosed.Statement.PretorsionTheory
