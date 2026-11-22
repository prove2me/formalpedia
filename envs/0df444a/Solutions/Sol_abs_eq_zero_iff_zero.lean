-- Prove2me | solution 1 for abs_eq_zero_iff_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:51.146092+00:00
-- url     : https://prove2.me/submissions/ae4fc9dd-e8be-4a7b-a876-ac17b21ddeec

module
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable (x : X)
theorem _root_.solution : |x| = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [← negPart_add_posPart, add_eq_zero_iff_eq_neg] at h
    have h1 : x⁺ = 0 := by
      apply le_antisymm
      · rw [← neg_zero]
        apply le_neg_of_le_neg
        rw [← h]
        exact negPart_nonneg x
      · exact posPart_nonneg x
    have h2 : x⁻ = 0 := by
      apply le_antisymm
      · rw [h]
        apply neg_le_of_neg_le
        rw [neg_zero]
        exact posPart_nonneg x
      · exact negPart_nonneg x
    rw [← posPart_sub_negPart x]
    rw [h1, h2]
    simp
  · intro h
    simp [h]
