-- Prove2me | solution 1 for card_rectPtSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:06:45.203037+00:00
-- url     : https://prove2.me/submissions/12393c7b-da0f-4089-80ed-2433f277e761

module
public import Definitions.Def_ScoutForbiddenMatrixContainment
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Definitions.Def_ForbiddenMatrix_ExtremalFunction
public import Theorems.Thm_density_mono
public import Theorems.Thm_ex_zero
public import Theorems.Thm_card_interval
public import Theorems.Thm_contains_of_isEmpty
attribute [local simp] contains_of_isEmpty


attribute [local gcongr] density_mono
attribute [local simp] ex_zero

set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}
theorem _root_.solution (n a₁ b₁ a₂ b₂ : ℕ) (h : b₁ ≤ n ∧ b₂ ≤ n) :
    #(rectPtset n a₁ b₁ a₂ b₂) = (b₁ - a₁) * (b₂ - a₂) := by
  simp only [rectPtset, card_product]
  suffices claim : ∀ x y, y ≤ n → #{a : Fin n | ↑a ∈ Finset.Ico x y} = #(.Ico x y) by aesop
  intro x y hy
  exact card_interval x y hy
