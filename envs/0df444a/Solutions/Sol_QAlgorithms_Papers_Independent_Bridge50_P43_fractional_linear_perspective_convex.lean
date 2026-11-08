-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P43.fractional_linear_perspective_convex
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:43:29.089922+00:00
-- url     : https://prove2.me/submissions/fad58c73-1450-4041-9755-32c8f503efc4

import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Set

theorem solution (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ioi 1) f) :
    ConvexOn ℝ (Set.Ioo 0 1) (fun u => (1-u) * f (1/(1-u))) := by
  refine ⟨convex_Ioo 0 1, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul]
  let A := 1 - x
  let B := 1 - y
  let C := 1 - (u * x + v * y)
  have hA : 0 < A := sub_pos.mpr hx.2
  have hB : 0 < B := sub_pos.mpr hy.2
  have hm : u * x + v * y ∈ Ioo (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using (convex_Ioo (0 : ℝ) 1) hx hy hu hv huv
  have hC : 0 < C := sub_pos.mpr hm.2
  have hlin : C = u * A + v * B := by dsimp [A,B,C]; nlinarith [huv]
  have hs : u * A / C + v * B / C = 1 := by
    rw [← add_div, ← hlin]; exact div_self (ne_of_gt hC)
  have harg : (u * A / C) * (1 / A) + (v * B / C) * (1 / B) = 1 / C := by
    field_simp
    nlinarith [huv]
  have hj := hf.2 (show 1 / A ∈ Ioi (1 : ℝ) by
      apply (lt_div_iff₀ hA).mpr; dsimp [A]; linarith [hx.1])
    (show 1 / B ∈ Ioi (1 : ℝ) by
      apply (lt_div_iff₀ hB).mpr; dsimp [B]; linarith [hy.1])
    (div_nonneg (mul_nonneg hu hA.le) hC.le)
    (div_nonneg (mul_nonneg hv hB.le) hC.le) hs
  simp only [smul_eq_mul] at hj
  rw [harg] at hj
  have hr := mul_le_mul_of_nonneg_left hj hC.le
  have heq : C * ((u * A / C) * f (1 / A) + (v * B / C) * f (1 / B)) =
      u * (A * f (1 / A)) + v * (B * f (1 / B)) := by field_simp
  rw [heq] at hr
  exact hr

#print axioms solution
