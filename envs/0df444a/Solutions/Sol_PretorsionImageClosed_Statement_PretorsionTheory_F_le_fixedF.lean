-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.F_le_fixedF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:48:45.940035+00:00
-- url     : https://prove2.me/submissions/77d38670-1f11-4eae-b21a-f8bb1466b160

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meetT_le
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_prop_of_mono_of_meetT
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_prop_iff_prop_trace


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
omit hP₀
namespace PretorsionImageClosed.Statement.PretorsionTheory
theorem _root_.solution {P : PretorsionTheory C} (hP : P ∈ S) : P.F ≤ fixedF S Z := by
  intro Y hY
  have hle : (meetT S).trace Y ≤ P.T.trace Y :=
    le_trace P.isPretorsionTheory.isQuotientClosed (meetT_le S hP _ ((meetT S).prop_trace Y))
  have hZ : Z.prop (P.T.trace Y : C) := by
    rw [← hS P hP]
    exact (P.isPretorsionTheory.prop_iff_prop_trace Y).1 hY
  exact prop_of_mono_of_meetT hP hS (Subobject.ofLE _ _ hle) ((meetT S).prop_trace Y) hZ
end PretorsionImageClosed.Statement.PretorsionTheory
