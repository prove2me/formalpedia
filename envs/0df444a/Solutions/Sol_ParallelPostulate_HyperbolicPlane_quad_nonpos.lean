-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.quad_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:21.85434+00:00
-- url     : https://prove2.me/submissions/d3f4b5fc-f8d9-49a8-85fb-b0402e1eecb3

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

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (α β γ : K) (hγ : 0 < γ) :
    ∃ T : K, ∀ t : K, T ≤ t → α + β * t - γ * t ^ 2 ≤ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : K, c * γ = α ^ 2 + β ^ 2 + 2 := ⟨_, div_mul_cancel₀ _ hγ.ne'⟩
  have hc0 : 0 < c := by
    have h : 0 < c * γ := by
      rw [hc]
      positivity
    exact (mul_pos_iff_of_pos_right hγ).mp h
  refine ⟨c + 1, fun t ht => ?_⟩
  have h1 : 1 ≤ t := by linarith
  have h2 : α ^ 2 + β ^ 2 + 2 ≤ t * γ := by
    have h := mul_le_mul_of_nonneg_right (show c ≤ t by linarith) hγ.le
    linarith
  have h3 : (α ^ 2 + β ^ 2 + 2) * t ≤ t * γ * t := mul_le_mul_of_nonneg_right h2 (by linarith)
  have h4 : 0 ≤ (α ^ 2 + 1) * (t - 1) := mul_nonneg (by positivity) (by linarith)
  have h5 : 0 ≤ (β ^ 2 - β + 1) * t :=
    mul_nonneg (by nlinarith [sq_nonneg (β - 1), sq_nonneg β]) (by linarith)
  have h6 : α ≤ α ^ 2 + 1 := by nlinarith [sq_nonneg (α - 1), sq_nonneg α]
  nlinarith only [h3, h4, h5, h6]
end ParallelPostulate.HyperbolicPlane
