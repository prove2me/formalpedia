-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.sInf_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:53:36.665075+00:00
-- url     : https://prove2.me/submissions/bb7d35cc-8559-4f07-b9a9-4e7c24a6505c

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_F_le_fixedF
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_prop_of_meetT_fixedF
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isPretorsionTheory_fixedF
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meet_F
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_eq


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
theorem _root_.solution : (sInf S).middle = Z.prop := by
  rw [sInf_eq]
  funext X
  apply propext
  constructor
  · rintro ⟨hT, hF⟩
    have hmem : (fixedF S Z).prop X := (iInf_prop_iff _ X).1 hF
      ⟨fixedF S Z, isPretorsionTheory_fixedF hP₀ hS, fun P hP => F_le_fixedF hS hP⟩
    exact prop_of_meetT_fixedF hT hmem
  · intro hX
    refine ⟨?_, ?_⟩
    · show (meetT S).prop X
      rw [meetT, iInf_prop_iff]
      intro P
      have := hS P.1 P.2
      rw [← this] at hX
      exact hX.1
    · rw [meet_F, iInf_prop_iff]
      intro F
      have := hS P₀ hP₀
      rw [← this] at hX
      exact F.2.2 P₀ hP₀ X hX.2
end PretorsionImageClosed.Statement.PretorsionTheory
