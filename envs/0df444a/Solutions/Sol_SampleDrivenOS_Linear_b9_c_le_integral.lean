-- Prove2me | solution 1 for SampleDrivenOS.Linear.b9_c_le_integral
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:56:14.257882+00:00
-- url     : https://prove2.me/submissions/03e74370-83b5-48fa-8fb1-472a5151ea82

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

set_option autoImplicit false
open SampleDrivenOS.Linear

lemma ci_phi_cont (c : ℝ) : Continuous fun y : ℝ => y * (1 - c * Real.log y) := by
  have : (fun y : ℝ => y * (1 - c * Real.log y)) = fun y => y - c * (y * Real.log y) := by
    funext y; ring
  rw [this]
  exact continuous_id.sub (continuous_const.mul Real.continuous_mul_log)

lemma ci_phi_nonneg (c : ℝ) (hc : 0 ≤ c) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ y * (1 - c * Real.log y) := by
  have : Real.log y ≤ 0 := Real.log_nonpos hy0 hy1
  have : 0 ≤ 1 - c * Real.log y := by nlinarith
  positivity

/-- `y (1 - p log y) ≤ 1` on `[0,1]` for `p ∈ [0,1]`. -/
lemma ci_phi_le_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    y * (1 - p * Real.log y) ≤ 1 := by
  rcases hy0.eq_or_lt with h | h
  · subst h; simp
  · -- `-y log y ≤ 1 - y` from `log (1/y) ≤ 1/y - 1`
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / y by positivity)
    rw [Real.log_div (by norm_num) h.ne', Real.log_one] at h1
    have h2 : 1 / y * y = 1 := by field_simp
    have h3 : -(y * Real.log y) ≤ 1 - y := by nlinarith
    have h4 : y * Real.log y ≤ 0 := Real.mul_log_nonpos hy0 hy1
    nlinarith

/-- `y ↦ y (1 - p log y)` is monotone on `[0,1]` when `p ∈ (0,1)`. -/
lemma ci_phi_mono (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    MonotoneOn (fun y : ℝ => y * (1 - p * Real.log y)) (Set.Icc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (ci_phi_cont p).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : x ≠ 0 := hx.1.ne'
    exact ((differentiableAt_id.mul ((differentiableAt_const _).sub
      ((differentiableAt_const _).mul (Real.differentiableAt_log hx0))))).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hd : HasDerivAt (fun y : ℝ => y * (1 - p * Real.log y))
        (1 * (1 - p * Real.log x) + x * (0 - p * x⁻¹)) x :=
      (hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub
        ((Real.hasDerivAt_log hx0).const_mul p))
    rw [hd.deriv]
    have : x * (0 - p * x⁻¹) = -p := by
      rw [zero_sub, mul_neg, mul_comm p, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    rw [this]
    have : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
    nlinarith

theorem solution (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    cB9 s p ≤
      1 / p * (∫ y in (0 : ℝ)..1, 1 / (1 / (p * s) - 1 + y * (1 - p * Real.log y))) -
        s * (1 - p) := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hp0, hp1⟩ := hp
  set X : ℝ := 1 / (p * s) with hX
  have hX1 : 1 < X := by
    rw [hX, lt_div_iff₀ (by positivity)]
    nlinarith
  set h : ℝ → ℝ := fun y => X - 1 + y * (1 - p * Real.log y) with hh
  have hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < h y := by
    intro y hy
    have := ci_phi_nonneg p hp0.le y hy.1 hy.2
    simp only [hh]; linarith
  have hhmono : MonotoneOn h (Set.Icc 0 1) := by
    intro x hx y hy hxy
    have := ci_phi_mono p hp0 hp1 hx hy hxy
    simp only [hh]; linarith
  have hfc : ContinuousOn (fun y => 1 / h y) (Set.Icc 0 1) :=
    continuousOn_const.div ((continuous_const.add (ci_phi_cont p)).continuousOn)
      (fun y hy => (hpos y hy).ne')
  have hII : IntervalIntegrable (fun y => 1 / h y) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le zero_le_one]
  have hIab : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      IntervalIntegrable (fun y => 1 / h y) MeasureTheory.volume a b := by
    intro a b ha hb
    apply hII.mono_set
    rw [Set.uIcc_of_le zero_le_one]
    intro y hy
    rcases le_total a b with hab | hab
    · rw [Set.uIcc_of_le hab] at hy; exact ⟨le_trans ha.1 hy.1, le_trans hy.2 hb.2⟩
    · rw [Set.uIcc_of_ge hab] at hy; exact ⟨le_trans hb.1 hy.1, le_trans hy.2 ha.2⟩
  have hpowmem : ∀ n : ℕ, p ^ n ∈ Set.Icc (0 : ℝ) 1 :=
    fun n => ⟨by positivity, pow_le_one₀ hp0.le hp1.le⟩
  have hlogp : 1 - 1 / p ≤ Real.log p := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / p by positivity)
    rw [Real.log_div (by norm_num) hp0.ne', Real.log_one] at h1
    linarith
  -- per-term bound
  have hterm : ∀ i : ℕ, (p ^ i - p ^ (i + 1)) /
      (1 / (p * s) - 1 + p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))) ≤
      1 / p * ∫ y in p ^ (i + 2)..p ^ (i + 1), 1 / h y := by
    intro i
    set x : ℝ := p ^ (i + 1) with hx
    have hxmem := hpowmem (i + 1)
    have hx0 : 0 < x := by positivity
    -- `h x ≤ D`
    have hlogx : Real.log x = ((i : ℝ) + 1) * Real.log p := by
      rw [hx, Real.log_pow]; push_cast; ring
    have hD : h x ≤ X - 1 + x * (1 + ((i : ℝ) + 1) * (1 - p)) := by
      simp only [hh]
      rw [hlogx]
      have : -(p * (((i : ℝ) + 1) * Real.log p)) ≤ ((i : ℝ) + 1) * (1 - p) := by
        have hi : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
        have : p * (1 - 1 / p) = p - 1 := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hlogp hp0.le]
      nlinarith
    have hhx := hpos x hxmem
    -- `∫_{x p}^{x} 1/h ≥ (x - x p) / h x`
    have hxp : p ^ (i + 2) = x * p := by rw [hx]; ring
    have hle : p ^ (i + 2) ≤ x := by rw [hxp]; nlinarith
    have hint : (x - p ^ (i + 2)) * (1 / h x) ≤ ∫ y in p ^ (i + 2)..x, 1 / h y := by
      have := intervalIntegral.integral_mono_on hle intervalIntegrable_const
        (hIab _ _ (hpowmem (i + 2)) hxmem) (f := fun _ => 1 / h x) (fun y hy => by
          have hy' : y ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨le_trans (hpowmem (i + 2)).1 hy.1, le_trans hy.2 hxmem.2⟩
          have := hhmono hy' hxmem hy.2
          exact one_div_le_one_div_of_le (hpos y hy') this)
      simpa using this
    have hpi : p ^ i - p ^ (i + 1) = 1 / p * (x - p ^ (i + 2)) := by
      rw [hxp, hx]; field_simp; ring
    rw [hpi]
    have hDpos : 0 < X - 1 + x * (1 + ((i : ℝ) + 1) * (1 - p)) := lt_of_lt_of_le hhx hD
    have h1 : 1 / (X - 1 + x * (1 + ((i : ℝ) + 1) * (1 - p))) ≤ 1 / h x :=
      one_div_le_one_div_of_le hhx hD
    have h2 : 0 ≤ x - p ^ (i + 2) := by linarith
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (x - p ^ (i + 2)) / (X - 1 + x * (1 + ((i : ℝ) + 1) * (1 - p)))
        = (x - p ^ (i + 2)) * (1 / (X - 1 + x * (1 + ((i : ℝ) + 1) * (1 - p)))) := by ring
      _ ≤ (x - p ^ (i + 2)) * (1 / h x) := mul_le_mul_of_nonneg_left h1 h2
      _ ≤ _ := hint
  -- telescoping of the integrals
  have htele : ∀ N : ℕ, ∑ i ∈ Finset.range N, ∫ y in p ^ (i + 2)..p ^ (i + 1), 1 / h y =
      ∫ y in p ^ (N + 1)..p, 1 / h y := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, add_comm]
      have := intervalIntegral.integral_add_adjacent_intervals
        (hIab (p ^ (N + 2)) (p ^ (N + 1)) (hpowmem _) (hpowmem _))
        (hIab (p ^ (N + 1)) p (hpowmem _) ⟨hp0.le, hp1.le⟩)
      rw [this]
  have hnonneg : ∀ a b : ℝ, a ≤ b → a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ ∫ y in a..b, 1 / h y := by
    intro a b hab ha hb
    apply intervalIntegral.integral_nonneg hab
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans ha.1 hy.1, le_trans hy.2 hb.2⟩
    exact (one_div_pos.mpr (hpos y hy')).le
  have hpI : ∀ N : ℕ, ∫ y in p ^ (N + 1)..p, 1 / h y ≤ ∫ y in (0 : ℝ)..p, 1 / h y := by
    intro N
    have := intervalIntegral.integral_add_adjacent_intervals
      (hIab 0 (p ^ (N + 1)) ⟨le_refl 0, zero_le_one⟩ (hpowmem _))
      (hIab (p ^ (N + 1)) p (hpowmem _) ⟨hp0.le, hp1.le⟩)
    rw [← this]
    have := hnonneg 0 (p ^ (N + 1)) (hpowmem _).1 ⟨le_refl 0, zero_le_one⟩ (hpowmem _)
    linarith
  -- terms are nonnegative
  have htnn : ∀ i : ℕ, 0 ≤ (p ^ i - p ^ (i + 1)) /
      (1 / (p * s) - 1 + p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))) := by
    intro i
    have h1 : 0 ≤ p ^ i - p ^ (i + 1) := by
      have : p ^ (i + 1) ≤ p ^ i := pow_le_pow_of_le_one hp0.le hp1.le (Nat.le_succ i)
      linarith
    have h2 : 0 ≤ p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) := by
      have : 0 ≤ 1 - p := by linarith
      positivity
    have : 0 < 1 / (p * s) - 1 + p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) := by
      rw [← hX]; linarith
    positivity
  have hcB : cB9 s p ≤ 1 / p * ∫ y in (0 : ℝ)..p, 1 / h y := by
    unfold cB9
    apply Real.tsum_le_of_sum_range_le htnn
    intro N
    calc ∑ i ∈ Finset.range N, (p ^ i - p ^ (i + 1)) /
          (1 / (p * s) - 1 + p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))
        ≤ ∑ i ∈ Finset.range N, 1 / p * ∫ y in p ^ (i + 2)..p ^ (i + 1), 1 / h y :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = 1 / p * ∫ y in p ^ (N + 1)..p, 1 / h y := by rw [← Finset.mul_sum, htele]
      _ ≤ 1 / p * ∫ y in (0 : ℝ)..p, 1 / h y :=
          mul_le_mul_of_nonneg_left (hpI N) (by positivity)
  -- `∫_p^1 1/h ≥ (1-p) p s`
  have hp1I : (1 - p) * (p * s) ≤ ∫ y in p..1, 1 / h y := by
    have := intervalIntegral.integral_mono_on hp1.le intervalIntegrable_const
      (hIab p 1 ⟨hp0.le, hp1.le⟩ ⟨zero_le_one, le_refl 1⟩) (f := fun _ => p * s) (fun y hy => by
        have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hp0.le hy.1, hy.2⟩
        have h1 := ci_phi_le_one p hp0.le hp1.le y hy'.1 hy'.2
        have h2 : h y ≤ X := by simp only [hh]; linarith
        have h3 : p * s = 1 / X := by rw [hX]; field_simp
        rw [h3]
        exact one_div_le_one_div_of_le (hpos y hy') h2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hIab 0 p ⟨le_refl 0, zero_le_one⟩ ⟨hp0.le, hp1.le⟩)
    (hIab p 1 ⟨hp0.le, hp1.le⟩ ⟨zero_le_one, le_refl 1⟩)
  have hhdef : (fun y => 1 / (1 / (p * s) - 1 + y * (1 - p * Real.log y))) = fun y => 1 / h y := rfl
  rw [hhdef, ← hsplit]
  have e : 1 / p * ((1 - p) * (p * s)) = s * (1 - p) := by field_simp
  have : 1 / p * ((1 - p) * (p * s)) ≤ 1 / p * ∫ y in p..1, 1 / h y :=
    mul_le_mul_of_nonneg_left hp1I (by positivity)
  rw [mul_add]
  linarith
