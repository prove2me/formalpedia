-- Prove2me | solution 1 for P2M_abs_smul__56c684b926d9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:33.175938+00:00
-- url     : https://prove2.me/submissions/93a1c945-cb8e-4876-b108-60cefed3c4f4

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
public import Theorems.Thm_nonneg_smul_sup

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)
theorem _root_.solution (a : ℝ) : |a • x| = |a| • |x| := by
  by_cases ha : a ≥ 0
  · rw [abs_of_nonneg ha]
    rw [abs, abs]
    rw [nonneg_smul_sup x (-x) a ha]
    simp
  · have hna : a < 0 := by linarith
    rw [abs_of_neg hna]
    rw [abs, abs]
    rw [nonneg_smul_sup x (-x) (-a) (by linarith)]
    simp [sup_comm]
