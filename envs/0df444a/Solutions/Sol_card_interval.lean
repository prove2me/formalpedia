-- Prove2me | solution 1 for card_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:17.135569+00:00
-- url     : https://prove2.me/submissions/6e39dacb-3e3b-4905-968f-ec146eb70d50

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
theorem _root_.solution {n : ℕ} (x y : ℕ) (hy : y ≤ n) :
    #{a : Fin n | ↑a ∈ Finset.Ico x y} = #(.Ico x y) := by
  apply Finset.card_bij (fun (a : Fin n) _ ↦ ↑a) (by aesop) (by aesop) ?_
  intro b hb
  simp at hb
  exact ⟨⟨b, by omega⟩, by simpa⟩
