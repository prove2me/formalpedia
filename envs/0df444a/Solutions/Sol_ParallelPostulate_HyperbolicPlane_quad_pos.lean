-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.quad_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:51.631988+00:00
-- url     : https://prove2.me/submissions/4cd2d56f-def9-4e0d-ad9a-c0d474c79fa4

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
theorem _root_.solution (α β γ : K) (hα : 0 < α) (hγ : 0 ≤ γ) :
    ∃ t : K, 0 < t ∧ 0 < α + β * t - γ * t ^ 2 := by
  have hD : 0 < α + β ^ 2 + 1 + γ := by nlinarith [sq_nonneg β]
  obtain ⟨t, ht⟩ : ∃ t : K, t * (α + β ^ 2 + 1 + γ) = α := ⟨_, div_mul_cancel₀ _ hD.ne'⟩
  have ht0 : 0 < t := by
    have h : 0 < t * (α + β ^ 2 + 1 + γ) := by
      rw [ht]
      exact hα
    exact (mul_pos_iff_of_pos_right hD).mp h
  refine ⟨t, ht0, ?_⟩
  have hβ : 0 < β ^ 2 + β + 1 := by nlinarith [sq_nonneg (β + 1), sq_nonneg β]
  have h1 : 0 < (α + β ^ 2 + 1) * (α + β ^ 2 + 1 + γ + β) :=
    mul_pos (by nlinarith [sq_nonneg β]) (by linarith)
  have h2 : 0 ≤ γ * (β ^ 2 + β + 1 + γ) := mul_nonneg hγ (by linarith)
  have hX : (α + β ^ 2 + 1 + γ) ^ 2 * (α + β * t - γ * t ^ 2)
      = α * ((α + β ^ 2 + 1) * (α + β ^ 2 + 1 + γ + β) + γ * (β ^ 2 + β + 1 + γ)) := by
    linear_combination
      (β * (α + β ^ 2 + 1 + γ) - γ * (t * (α + β ^ 2 + 1 + γ) + α)) * ht
  have hpos : 0 < (α + β ^ 2 + 1 + γ) ^ 2 * (α + β * t - γ * t ^ 2) := by
    rw [hX]
    exact mul_pos hα (by linarith)
  exact (mul_pos_iff_of_pos_left (pow_pos hD 2)).mp hpos
end ParallelPostulate.HyperbolicPlane
