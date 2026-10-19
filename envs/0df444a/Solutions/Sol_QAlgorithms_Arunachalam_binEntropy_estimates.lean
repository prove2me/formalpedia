-- Prove2me | solution 1 for QAlgorithms.Arunachalam.binEntropy_estimates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:02:29.427704+00:00
-- url     : https://prove2.me/submissions/9c78dbfb-7fee-4b2e-8e4b-10996f94bc36

import Definitions.Def_QAlgorithms_Defs_Information
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Real Set QAlgorithms

private lemma decreasing_from_zero (f f' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) (1/4), HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc (0 : ℝ) (1/4), f' x ≤ 0)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1/4)) : f x ≤ f 0 := by
  have hc : ContinuousOn f (Icc (0 : ℝ) (1/4)) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have ha := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) (1/4)) hc
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => hn y (interior_subset hy))
  exact ha (by norm_num) hx hx.1

private lemma log_ratio_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/4) :
    log (1/2+x) - log (1/2-x) ≤ 4*x + 64*x^3 := by
  have hd : ∀ y ∈ Icc (0 : ℝ) (1/4),
      HasDerivAt (fun y : ℝ => log (1/2+y) - log (1/2-y) - 4*y - 64*y^3)
        ((1/2+y)⁻¹ + (1/2-y)⁻¹ - 4 - 192*y^2) y := by
    intro y hy
    have hp : (1/2:ℝ)+y ≠ 0 := by linarith [hy.1]
    have hm : (1/2:ℝ)-y ≠ 0 := by linarith [hy.2]
    convert! ((((hasDerivAt_const y (1/2:ℝ)).add (hasDerivAt_id y)).log hp).sub
      (((hasDerivAt_const y (1/2:ℝ)).sub (hasDerivAt_id y)).log hm) |>.sub
      ((hasDerivAt_id y).const_mul 4)).sub
      (((hasDerivAt_id y).pow 3).const_mul 64) using 1 <;>
      simp only [Pi.add_apply, Pi.sub_apply, id_eq] <;> ring
  have hn : ∀ y ∈ Icc (0 : ℝ) (1/4),
      (1/2+y)⁻¹ + (1/2-y)⁻¹ - 4 - 192*y^2 ≤ 0 := by
    intro y hy
    have hp : 0 < (1/2:ℝ)+y := by linarith [hy.1]
    have hm : 0 < (1/2:ℝ)-y := by linarith [hy.2]
    have hs : y^2 ≤ 1/16 := by nlinarith [hy.1, hy.2]
    have he : (1/2+y)⁻¹ + (1/2-y)⁻¹ - 4 - 192*y^2 =
        (192*y^4 - 44*y^2) / ((1/2+y)*(1/2-y)) := by
      apply (eq_div_iff (mul_pos hp hm).ne').2
      linear_combination (1/2-y) * (inv_mul_cancel₀ hp.ne') +
        (1/2+y) * (inv_mul_cancel₀ hm.ne')
    rw [he]
    apply div_nonpos_of_nonpos_of_nonneg _ (mul_pos hp hm).le
    nlinarith [mul_nonneg (sq_nonneg y) (show 44-192*y^2 ≥ 0 by nlinarith)]
  have h := decreasing_from_zero _ _ hd hn x ⟨hx0,hx1⟩
  norm_num at h
  linarith

private lemma entropy_remainder (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/4) :
    log 2 - binEntropy (1/2+x) ≤ 2*x^2 + 16*x^4 := by
  have hd : ∀ y ∈ Icc (0 : ℝ) (1/4),
      HasDerivAt (fun y : ℝ => log 2 - binEntropy (1/2+y) - 2*y^2 - 16*y^4)
        (log (1/2+y) - log (1/2-y) - 4*y - 64*y^3) y := by
    intro y hy
    have hp : (1/2:ℝ)+y ≠ 0 := by linarith [hy.1]
    have hm : (1/2:ℝ)+y ≠ 1 := by linarith [hy.2]
    have hb := (hasDerivAt_binEntropy hp hm).comp y
      ((hasDerivAt_const y (1/2:ℝ)).add (hasDerivAt_id y))
    convert! (((hasDerivAt_const y (log 2)).sub hb).sub
      (((hasDerivAt_id y).pow 2).const_mul 2)).sub
      (((hasDerivAt_id y).pow 4).const_mul 16) using 1
    simp only [id_eq]
    rw [show (1:ℝ)-(1/2+y)=1/2-y by ring]
    ring
  have h := decreasing_from_zero _ _ hd
    (fun y hy => by linarith [log_ratio_bound y hy.1 hy.2]) x ⟨hx0,hx1⟩
  have hb : binEntropy (1/2) = log 2 := by
    convert binEntropy_two_inv using 1 <;> norm_num
  norm_num [hb] at h
  linarith

theorem solution :
    (∃ C₁ : ℝ, 0 < C₁ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 →
        binEntropy2 ε ≤ C₁ * (ε * Real.logb 2 (1 / ε))) ∧
      ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 →
        1 - binEntropy2 (1 / 2 + ε) ≤ 2 * ε ^ 2 / Real.log 2 + C₂ * ε ^ 4 := by
  have hL : 0 < log (2:ℝ) := log_pos (by norm_num)
  constructor
  · refine ⟨1 + 1/log 2, by positivity, ?_⟩
    intro ε hε0 hε1
    rcases eq_or_lt_of_le hε0 with rfl | hε
    · simp [binEntropy2, Real.logb]
    have hm : 0 < 1-ε := by linarith
    have hl := mul_le_mul_of_nonneg_left
      (log_le_sub_one_of_pos (inv_pos.mpr hm)) hm.le
    have he : (1-ε)*((1-ε)⁻¹-1) = ε := by field_simp; ring
    rw [he] at hl
    have hlog : log 2 ≤ log (1/ε) := by
      apply log_le_log (by norm_num)
      exact (le_div_iff₀ hε).2 (by linarith)
    have hh : ε ≤ (ε*log (1/ε))/log 2 :=
      (le_div_iff₀ hL).2 (by nlinarith)
    have hb : binEntropy ε ≤ (1 + 1/log 2)*(ε*log (1/ε)) := by
      rw [binEntropy]
      simp only [div_eq_mul_inv, one_mul] at hh ⊢
      nlinarith
    simpa only [binEntropy2, Real.logb, mul_div_assoc] using
      div_le_div_of_nonneg_right hb hL.le
  · refine ⟨256 + 16/log 2, by positivity, ?_⟩
    intro ε hε0 hε1
    by_cases hs : ε ≤ 1/4
    · have h := div_le_div_of_nonneg_right (entropy_remainder ε hε0 hs) hL.le
      have he : (log 2 - binEntropy (1/2+ε))/log 2 =
          1 - binEntropy2 (1/2+ε) := by
        rw [sub_div, div_self hL.ne', binEntropy2]
      rw [he] at h
      have hp : 0 ≤ ε^4 := by positivity
      calc
        1 - binEntropy2 (1/2+ε) ≤ (2*ε^2+16*ε^4)/log 2 := h
        _ ≤ 2*ε^2/log 2 + (256+16/log 2)*ε^4 := by
          simp only [div_eq_mul_inv]
          nlinarith
    · have he : (1/4:ℝ) ≤ ε := le_of_not_ge hs
      have hp : (1/256:ℝ) ≤ ε^4 := by
        have h2 : (1/16:ℝ) ≤ ε^2 := by nlinarith
        nlinarith [sq_nonneg (ε^2-1/16)]
      have hn : 0 ≤ binEntropy2 (1/2+ε) :=
        div_nonneg (binEntropy_nonneg (by linarith) (by linarith)) hL.le
      have ht : 0 ≤ 2*ε^2/log 2 := by positivity
      have hu : 0 ≤ (16/log 2)*ε^4 := by positivity
      nlinarith
