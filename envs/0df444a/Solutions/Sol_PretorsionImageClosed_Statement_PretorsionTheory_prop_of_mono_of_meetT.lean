-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.prop_of_mono_of_meetT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:47:57.659369+00:00
-- url     : https://prove2.me/submissions/b6c0f19f-f455-4800-83e6-4add6cd6aed1

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meetT_le
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed


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
theorem _root_.solution {M N : C} (i : M ⟶ N) [Mono i] (hM : (meetT S).prop M)
    (hN : Z.prop N) : Z.prop M := by
  have hmid := hS P₀ hP₀
  rw [← hmid] at hN ⊢
  exact ⟨meetT_le S hP₀ M hM, P₀.isPretorsionTheory.isSubobjectClosed i inferInstance hN.2⟩
end PretorsionImageClosed.Statement.PretorsionTheory
