-- Prove2me | solution 1 for OnlineBeckFiala.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:11:11.919388+00:00
-- url     : https://prove2.me/submissions/3534c85b-51d4-4245-aac5-23fb63f2bd79

import Mathlib
import Definitions.Def_OnlineBeckFiala_IsBalanced

section
open MeasureTheory

namespace OnlineBeckFiala

namespace Dev.L25

theorem ratio {n : ℕ} (u : ℝ → ℝ) (L : ℝ) (hZ : 0 < Zu u) (x y : Fin n → ℝ)
    (hx : x ∈ cube L) (hy : y ∈ cube L) :
    uDensity u L y / uDensity u L x = Real.exp (-(∑ i, (u (y i / L) - u (x i / L)))) := by
  unfold uDensity prodDensity
  rw [← Finset.prod_div_distrib, Real.exp_neg, Real.exp_sum, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hL : 0 < L := by
    have := hx i
    linarith [this.1, this.2]
  unfold uRho
  rw [Set.indicator_of_mem (hy i), Set.indicator_of_mem (hx i)]
  have hc : ((L * Zu u)⁻¹) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ hc, ← Real.exp_sub, ← Real.exp_neg]
  congr 1
  ring

theorem key (A B : ℝ) (h : A + B ≤ 2 * Real.log 2) :
    1 ≤ min 1 (Real.exp (-A)) + min 1 (Real.exp (-B)) := by
  have hA := Real.exp_pos (-A)
  have hB := Real.exp_pos (-B)
  by_cases h1 : A ≤ 0
  · have : min 1 (Real.exp (-A)) = 1 := min_eq_left (by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith))
    rw [this]; have := le_min zero_le_one hB.le; linarith
  by_cases h2 : B ≤ 0
  · have : min 1 (Real.exp (-B)) = 1 := min_eq_left (by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith))
    rw [this]; have := le_min zero_le_one hA.le; linarith
  push_neg at h1 h2
  rw [min_eq_right (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)),
    min_eq_right (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith))]
  set s := Real.exp (-A / 2)
  set t := Real.exp (-B / 2)
  have hs : Real.exp (-A) = s * s := by
    simp only [s]; rw [← Real.exp_add]; congr 1; ring
  have ht : Real.exp (-B) = t * t := by
    simp only [t]; rw [← Real.exp_add]; congr 1; ring
  have hst : s * t = Real.exp (-(A + B) / 2) := by
    simp only [s, t]; rw [← Real.exp_add]; congr 1; ring
  have hge : (1 / 2 : ℝ) ≤ Real.exp (-(A + B) / 2) := by
    have : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [← this]; exact Real.exp_le_exp.2 (by linarith)
  rw [hs, ht]
  nlinarith [sq_nonneg (s - t)]

end Dev.L25

theorem chk_lemma_2_5 {n : ℕ} (u : ℝ → ℝ) (L : ℝ)
    (hu : IntegrableOn (fun y => Real.exp (-u y)) (Set.Ioo (-1) 1))
    (x v : Fin n → ℝ) (hplus : x + v ∈ cube L) (hminus : x - v ∈ cube L)
    (hD : Dv u L x v ≤ 2 * Real.log 2) :
    IsBalanced L (uDensity u L) v x := by
  have hx : x ∈ cube L := by
    intro i
    have h1 := hplus i
    have h2 := hminus i
    simp only [Pi.add_apply, Pi.sub_apply] at h1 h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨hx, ?_⟩
  have hZ : 0 < Zu u := by
    unfold Zu
    have : NeZero (volume.restrict (Set.Ioo (-1 : ℝ) 1)) := ⟨by
      simp [Measure.restrict_eq_zero]⟩
    have := integral_exp_pos (μ := volume.restrict (Set.Ioo (-1 : ℝ) 1)) (f := fun y => -u y)
      hu
    exact this
  have h1 := Dev.L25.ratio u L hZ x (x + v) hx hplus
  have h2 := Dev.L25.ratio u L hZ x (x - v) hx hminus
  have e1 : (∑ i, (u ((x + v) i / L) - u (x i / L))) = Delta u L 1 x v := by
    unfold Delta; simp
  have e2 : (∑ i, (u ((x - v) i / L) - u (x i / L))) = Delta u L (-1) x v := by
    unfold Delta; simp [sub_eq_add_neg]
  rw [e1] at h1
  rw [e2] at h2
  unfold pPlus pMinus
  rw [h1, h2]
  have := Dev.L25.key (Delta u L 1 x v) (Delta u L (-1) x v) hD
  linarith

end OnlineBeckFiala

end

theorem solution : type_of% @OnlineBeckFiala.chk_lemma_2_5 := @OnlineBeckFiala.chk_lemma_2_5
