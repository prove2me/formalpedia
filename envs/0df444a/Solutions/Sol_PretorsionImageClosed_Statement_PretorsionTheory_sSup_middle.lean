-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.sSup_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:22.803237+00:00
-- url     : https://prove2.me/submissions/169986eb-7315-4df1-9739-69a5cb15877c

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_unop_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_eq
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_eq_join


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
theorem _root_.solution : (sSup S).middle = Z.prop := by
  rw [sSup_eq_join, join, unop_middle]
  have h := sInf_middle (S := PretorsionTheory.op '' S) (Z := Z.op) ⟨P₀, hP₀, rfl⟩ (by
    rintro _ ⟨P, hP, rfl⟩
    rw [op_middle, hS P hP]
    rfl)
  rw [sInf_eq] at h
  rw [h]
  rfl
end PretorsionImageClosed.Statement.PretorsionTheory
