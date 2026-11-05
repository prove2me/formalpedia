-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P45.lemmaII5
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:23:21.585506+00:00
-- url     : https://prove2.me/submissions/17b8c56a-80e5-40bb-a0d7-8ac3e7f6fdf0

import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Set

theorem solution (J Jprime K : Set ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (hJ : Convex ℝ J) (hpositive : J ⊆ Ioi 0) (hf : ConvexOn ℝ J f)
    (hJprime : Convex ℝ Jprime) (hphi : ∀ t ∈ Jprime, a*t+b ∈ J)
    (hK : Convex ℝ K) (hsub : K ⊆ Jprime)
    (hdefined : ∀ t ∈ K, 0 < a*t+b ∧ (a*t+b)⁻¹ ∈ J)
    (hcontinuous : ContinuousOn f ((fun t => a*t+b) '' Jprime)) :
    ConvexOn ℝ K (fun t => (a*t+b) * f ((a*t+b)⁻¹)) := by
  refine ⟨hK, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul]
  let A := a * x + b
  let B := a * y + b
  let C := a * (u * x + v * y) + b
  have hA : 0 < A := (hdefined x hx).1
  have hB : 0 < B := (hdefined y hy).1
  have hmix : u * x + v * y ∈ K := by
    simpa only [smul_eq_mul] using hK hx hy hu hv huv
  have hC : 0 < C := (hdefined _ hmix).1
  have hlin : C = u * A + v * B := by dsimp [A, B, C]; linear_combination -b * huv
  have hsum : u * A / C + v * B / C = 1 := by rw [← add_div, ← hlin]; exact div_self (ne_of_gt hC)
  have harg : (u * A / C) * A⁻¹ + (v * B / C) * B⁻¹ = C⁻¹ := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]
    nlinarith [huv]
  have hj := hf.2 (hdefined x hx).2 (hdefined y hy).2
    (div_nonneg (mul_nonneg hu hA.le) hC.le)
    (div_nonneg (mul_nonneg hv hB.le) hC.le) hsum
  simp only [smul_eq_mul] at hj
  rw [harg] at hj
  have hm := mul_le_mul_of_nonneg_left hj hC.le
  have heq : C * ((u * A / C) * f A⁻¹ + (v * B / C) * f B⁻¹) =
      u * (A * f A⁻¹) + v * (B * f B⁻¹) := by field_simp [ne_of_gt hC] <;> ring
  rw [heq] at hm
  exact hm

#print axioms solution
