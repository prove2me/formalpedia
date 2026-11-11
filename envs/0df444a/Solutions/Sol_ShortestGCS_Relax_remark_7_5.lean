-- Prove2me | solution 1 for ShortestGCS.Relax.remark_7_5
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-10T12:32:23.889796+00:00
-- url     : https://prove2.me/submissions/d3551f76-734e-4f70-984e-de7a3d10ddb9

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution {m : ℕ} (Y : Set (Fin m → ℝ)) (hY : Y ⊆ {y | ∀ i, y i ∈ Set.Icc (0 : ℝ) 1}) :
    ∀ y ∈ Y, (∀ i, y i = 0 ∨ y i = 1) → y ∈ Set.extremePoints ℝ Y := by
  intro y hy hbinary
  refine mem_extremePoints_iff_left.mpr ⟨hy, ?_⟩
  intro x hx z hz hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  funext i
  have hx' : x i ∈ Set.Icc (0 : ℝ) 1 := hY hx i
  have hz' : z i ∈ Set.Icc (0 : ℝ) 1 := hY hz i
  have hcomb := congrFun heq i
  change a * x i + b * z i = y i at hcomb
  rcases hbinary i with hzero | hone
  · have hp : a * x i = 0 := by
      nlinarith [mul_nonneg ha.le hx'.1, mul_nonneg hb.le hz'.1]
    rw [hzero]
    exact (mul_eq_zero.mp hp).resolve_left ha.ne'
  · have hp : a * (1 - x i) = 0 := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hx'.2),
        mul_nonneg hb.le (sub_nonneg.mpr hz'.2)]
    rw [hone]
    linarith [(mul_eq_zero.mp hp).resolve_left ha.ne']

#print axioms solution