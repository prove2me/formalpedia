-- Prove2me | solution 1 for RandomOrderCRS.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:54:13.118698+00:00
-- url     : https://prove2.me/submissions/ff7e12ff-0b74-474e-9b19-9b299fd550c8

import Mathlib
import Definitions.Def_RandomOrderCRS_Attenuation

open Real

namespace Aux_RandomOrderCRS_proposition_8

lemma key (c t y : ℝ) (hc1 : 1/4 < c) (hc2 : c < 2/7) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ (4*c - 6*c^2*t) * (1 - y*(t*((1-c*t)*(1-c*t)))) - y*(1 - 4*c*t + 3*c^2*(t*t))^2 := by
  have hcpos : 0 < c := by linarith
  have hA : 0 ≤ 4*c - 6*c^2*t := by
    have h1 : c^2*t ≤ c^2 := by
      have := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr ht1)
      nlinarith
    have h2 : 0 < c * (2/3 - c) := mul_pos hcpos (by linarith)
    nlinarith
  obtain ⟨s, hs⟩ : ∃ s, s = c*t := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact mul_nonneg hcpos.le ht0
  have hsc : s ≤ c := by rw [hs]; exact mul_le_of_le_one_right hcpos.le ht1
  have hP : 0 ≤ (4*c - 6*c^2*t) * (1 - (t*((1-c*t)*(1-c*t)))) - (1 - 4*c*t + 3*c^2*(t*t))^2 := by
    have e : (4*c - 6*c^2*t) * (1 - (t*((1-c*t)*(1-c*t)))) - (1 - 4*c*t + 3*c^2*(t*t))^2
        = (4*c - 1) + s*(4 - 6*c - 8*s) + s^3*(8 - 3*s) := by rw [hs]; ring
    rw [e]
    have h1 : 0 ≤ s*(4 - 6*c - 8*s) := mul_nonneg hs0 (by linarith)
    have h2 : 0 ≤ s^3*(8 - 3*s) := mul_nonneg (pow_nonneg hs0 3) (by linarith)
    linarith
  have e2 : (4*c - 6*c^2*t) * (1 - y*(t*((1-c*t)*(1-c*t)))) - y*(1 - 4*c*t + 3*c^2*(t*t))^2
      = (1-y)*(4*c - 6*c^2*t)
        + y*((4*c - 6*c^2*t) * (1 - (t*((1-c*t)*(1-c*t)))) - (1 - 4*c*t + 3*c^2*(t*t))^2) := by
    ring
  rw [e2]
  have h3 := mul_nonneg (sub_nonneg.mpr hy1) hA
  have h4 := mul_nonneg hy0 hP
  linarith

lemma gpos (c t y : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < 1 - y*(t*((1-c*t)*(1-c*t))) := by
  have hct : c*t ≤ 1 := by nlinarith
  have hct0 : 0 ≤ c*t := mul_nonneg hc.le ht0
  have hu0 : 0 ≤ 1 - c*t := by linarith
  have hu1 : 1 - c*t ≤ 1 := by linarith
  have ha : (1-c*t)*(1-c*t) ≤ 1 - c*t := by nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu1)]
  have hb : t*((1-c*t)*(1-c*t)) ≤ t*(1-c*t) := mul_le_mul_of_nonneg_left ha ht0
  have hq0 : 0 ≤ t*((1-c*t)*(1-c*t)) := mul_nonneg ht0 (mul_nonneg hu0 hu0)
  have hyq : y*(t*((1-c*t)*(1-c*t))) ≤ t*((1-c*t)*(1-c*t)) := by
    have := mul_nonneg (sub_nonneg.mpr hy1) hq0
    nlinarith
  have h5 : 0 < 1 - t + c*t^2 := by
    have := mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr ht1)
    have := mul_nonneg hc.le (sq_nonneg (t - 1/2))
    nlinarith
  nlinarith

end Aux_RandomOrderCRS_proposition_8

open Aux_RandomOrderCRS_proposition_8 in
open RandomOrderCRS in
theorem solution :
    (∀ y ∈ Set.Icc (0 : ℝ) 1, ConvexOn ℝ (Set.Icc (0 : ℝ) 1) fun t => log (1 - y * t * a₁ t)) ∧
    a₁ 0 = 1 ∧ ContinuousOn a₁ (Set.Icc (0 : ℝ) 1) ∧ StrictAntiOn a₁ (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨c, hc⟩ : ∃ c, c = 3 - exp 1 := ⟨_, rfl⟩
  have hc1 : 1/4 < c := by rw [hc]; linarith [Real.exp_one_lt_d9]
  have hc2 : c < 2/7 := by rw [hc]; linarith [Real.exp_one_gt_d9]
  have hcpos : 0 < c := by linarith
  have hA : ∀ t, a₁ t = (1 - c*t)^2 := by intro t; rw [hc]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hfun : (fun t => log (1 - y * t * a₁ t))
        = fun t => log (1 - y*(t*((1-c*t)*(1-c*t)))) := by
      funext t; rw [hA]; congr 1; ring
    rw [hfun]
    have hg : ∀ x : ℝ, HasDerivAt (fun t => 1 - y*(t*((1-c*t)*(1-c*t))))
        (-y*(1 - 4*c*x + 3*c^2*(x*x))) x := by
      intro x
      have hL := ((hasDerivAt_id' x).const_mul c).const_sub 1
      have hG := (((hasDerivAt_id' x).mul (hL.mul hL)).const_mul y).const_sub 1
      exact hG.congr_deriv (by simp only [Pi.mul_apply]; ring)
    have hN : ∀ x : ℝ, HasDerivAt (fun t => -y*(1 - 4*c*t + 3*c^2*(t*t)))
        (y*(4*c - 6*c^2*x)) x := by
      intro x
      have h1 := (((hasDerivAt_id' x).const_mul (4*c)).const_sub 1).add
        (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).const_mul (3*c^2))
      have h2 := h1.const_mul (-y)
      exact h2.congr_deriv (by ring)
    have hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < 1 - y*(x*((1-c*x)*(1-c*x))) := by
      intro x hx
      exact gpos c x y hcpos (by linarith) hx.1 hx.2 hy0 hy1
    have hint : interior (Set.Icc (0:ℝ) 1) = Set.Ioo 0 1 := interior_Icc
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (f' := fun x => (-y*(1 - 4*c*x + 3*c^2*(x*x))) / (1 - y*(x*((1-c*x)*(1-c*x)))))
      (f'' := fun x => ((y*(4*c - 6*c^2*x)) * (1 - y*(x*((1-c*x)*(1-c*x))))
          - (-y*(1 - 4*c*x + 3*c^2*(x*x))) * (-y*(1 - 4*c*x + 3*c^2*(x*x))))
          / (1 - y*(x*((1-c*x)*(1-c*x))))^2) ?_ ?_ ?_ ?_
    · intro x hx
      exact ((hg x).log (hpos x hx).ne').continuousAt.continuousWithinAt
    · intro x hx
      rw [hint] at hx
      have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
      exact ((hg x).log (hpos x hx').ne').hasDerivWithinAt
    · intro x hx
      rw [hint] at hx
      have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
      exact ((hN x).fun_div (hg x) (hpos x hx').ne').hasDerivWithinAt
    · intro x hx
      rw [hint] at hx
      have hk := key c x y hc1 hc2 hx.1.le hx.2.le hy0 hy1
      apply div_nonneg _ (sq_nonneg _)
      have e : (y*(4*c - 6*c^2*x)) * (1 - y*(x*((1-c*x)*(1-c*x))))
          - (-y*(1 - 4*c*x + 3*c^2*(x*x))) * (-y*(1 - 4*c*x + 3*c^2*(x*x)))
          = y * ((4*c - 6*c^2*x) * (1 - y*(x*((1-c*x)*(1-c*x))))
              - y*(1 - 4*c*x + 3*c^2*(x*x))^2) := by ring
      rw [e]
      exact mul_nonneg hy0 hk
  · rw [hA]; ring
  · have : Continuous a₁ := by unfold a₁; fun_prop
    exact this.continuousOn
  · intro a ha b hb hab
    rw [hA, hA]
    have h1 : 0 < 1 - c*b := by
      have := mul_le_of_le_one_right hcpos.le hb.2
      linarith
    have h2 : c*a < c*b := mul_lt_mul_of_pos_left hab hcpos
    nlinarith [mul_pos (sub_pos.mpr h2) (by linarith : (0:ℝ) < (1 - c*a) + (1 - c*b))]
