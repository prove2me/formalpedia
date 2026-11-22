-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.crosses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:46.386398+00:00
-- url     : https://prove2.me/submissions/41202da7-da7c-4a5f-a2ec-bf501926053e

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_side_through
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_mem_points_of_side_eq_zero
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_convex
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ : K) (M : Dim K) (hM : M.zero ≠ M.one) {P Q : K × K} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) (h : M.side P * M.side Q < 0) :
    ∃ Y : K × K, Y ∈ M.points ∧ Y ∈ plane κ ∧ Between P Y Q := by
  have hf0 : M.side P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact lt_irrefl _ h
  have hf2 : 0 < M.side P ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hf0).symm
  have hden : 0 < M.side P ^ 2 - M.side P * M.side Q := by linarith
  obtain ⟨v, hv⟩ : ∃ v : K, v * (M.side P ^ 2 - M.side P * M.side Q) = M.side P ^ 2 :=
    ⟨_, div_mul_cancel₀ _ hden.ne'⟩
  have hv0 : 0 < v := by
    have h' : 0 < v * (M.side P ^ 2 - M.side P * M.side Q) := by
      rw [hv]
      exact hf2
    exact (mul_pos_iff_of_pos_right hden).mp h'
  have hv1 : v < 1 := by
    by_contra hcon
    have h' := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hden.le
    linarith
  have hPQ : P ≠ Q := by
    intro h'
    rw [h'] at h
    exact absurd h (not_lt.mpr (mul_self_nonneg _))
  refine ⟨(Dim.mk P Q).pt v, ?_, plane_convex κ hP hQ hv0.le hv1.le, hPQ, v, hv0, hv1, rfl⟩
  apply M.mem_points_of_side_eq_zero hM
  rw [M.side_through]
  have h0 : M.side P * ((1 - v) * M.side P + v * M.side Q) = 0 := by
    linear_combination -hv
  exact (mul_eq_zero.mp h0).resolve_left hf0
end ParallelPostulate.HyperbolicPlane
