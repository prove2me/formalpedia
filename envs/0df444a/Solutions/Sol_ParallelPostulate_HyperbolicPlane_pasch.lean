-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.pasch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:24.750514+00:00
-- url     : https://prove2.me/submissions/778c0f0f-5986-49f7-8ca1-2b5e8081faf9

module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_side_eq_zero_of_mem
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_side_through
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_mem_points_of_side_eq_zero
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_crosses

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ : K) {A B C : K × K} (hA : A ∈ plane κ) (hB : B ∈ plane κ)
    (hC : C ∈ plane κ) (M : Dim K) (hM : M.zero ≠ M.one) (hAM : A ∉ M.points)
    (hBM : B ∉ M.points) (hCM : C ∉ M.points) {X : K × K} (hX : X ∈ M.points)
    (hAXB : Between A X B) :
    ∃ Y : K × K, Y ∈ M.points ∧ Y ∈ plane κ ∧ (Between A Y C ∨ Between B Y C) := by
  have fA : M.side A ≠ 0 := fun h => hAM (M.mem_points_of_side_eq_zero hM A h)
  have fB : M.side B ≠ 0 := fun h => hBM (M.mem_points_of_side_eq_zero hM B h)
  have fC : M.side C ≠ 0 := fun h => hCM (M.mem_points_of_side_eq_zero hM C h)
  have fA2 : 0 < M.side A ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 fA).symm
  have fB2 : 0 < M.side B ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 fB).symm
  obtain ⟨-, u, hu0, hu1, rfl⟩ := hAXB
  have hX0 := M.side_eq_zero_of_mem hX
  rw [M.side_through] at hX0
  have hAB : M.side A * M.side B < 0 := by
    have h1 : (1 - u) * (M.side A * M.side B) = -(u * M.side B ^ 2) := by
      linear_combination M.side B * hX0
    have h2 : 0 < u * M.side B ^ 2 := mul_pos hu0 fB2
    by_contra hcon
    have h3 := mul_nonneg (show (0 : K) ≤ 1 - u by linarith) (not_lt.mp hcon)
    linarith
  rcases lt_or_gt_of_ne (mul_ne_zero fA fC) with h | h
  · obtain ⟨Y, h1, h2, h3⟩ := crosses κ M hM hA hC h
    exact ⟨Y, h1, h2, Or.inl h3⟩
  · have hBC : M.side B * M.side C < 0 := by
      have h1 : M.side A ^ 2 * (M.side B * M.side C)
          = (M.side A * M.side B) * (M.side A * M.side C) := by ring
      have h2 : (M.side A * M.side B) * (M.side A * M.side C) < 0 :=
        mul_neg_of_neg_of_pos hAB h
      by_contra hcon
      have h3 := mul_nonneg fA2.le (not_lt.mp hcon)
      linarith
    obtain ⟨Y, h1, h2, h3⟩ := crosses κ M hM hB hC hBC
    exact ⟨Y, h1, h2, Or.inr h3⟩
end ParallelPostulate.HyperbolicPlane
