-- Prove2me | solution 1 for RybinAI2026.P01.j_closed_neg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T09:42:18.633167+00:00
-- url     : https://prove2.me/submissions/f54f20ee-dd36-4c88-b5d4-97ae6d5c73d7

-- Candidate v11 for j_closed_neg (repair-of 7198: drop redundant exact after congr closes step): drop stray top-level rw[e0] that pre-transformed the goal): congr-step-1 avoids rewrite-under-binder matching): ring closer on mul_comm residual): limit-order normalization): factor-first partial fractions): conv_lhs + ne-facts + Interval scope + calc align) — NOT a candidate, NEVER submit as-is.
-- Helper for future RybinAI2026.P01.h_sq_strict_concave candidate:
-- j(c) = artanh(sqrt(-c))/sqrt(-c) for c in (-1, 0), via partial fractions.
-- Route: 1/(1-k^2 t^2) = (1/2)[1/(1-kt) + 1/(1+kt)] (exact, checked),
-- linear substitutions (integral_comp_mul_left / comp_add_right /
-- comp_sub_left — all verified present in pinned revs), integral_inv_of_pos,
-- artanh_eq_half_log. Closed form matches direct quadrature to 1e-12.
-- Names verified present (c5ea003 tree + 0df444a index where noted) on 2026-10-05:
-- integral_comp_mul_left, integral_comp_add_right, integral_comp_sub_left
-- (also PRESENT_IN_PINNED_INDEX @0df444a), integral_inv_of_pos,
-- Real.artanh_eq_half_log, intervalIntegral.integral_congr_ae
-- (forall-ae-with-membership form), Continuous.intervalIntegrable [VERIFY at assembly].
-- Remote verification still required after integration into the full proof.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral
open scoped Interval

-- j(c) closed form for c in (-1, 0) (Step 1, negative case).
theorem solution (c : ℝ) (hc1 : -1 < c) (hc0 : c < 0) :
    (∫ t in (0 : ℝ)..1, ((1 : ℝ) + c * t ^ 2)⁻¹)
      = Real.artanh (Real.sqrt (-c)) / Real.sqrt (-c) := by
  have hnc : (0 : ℝ) < -c := neg_pos.mpr hc0
  have hk0 : (0 : ℝ) < Real.sqrt (-c) := Real.sqrt_pos.mpr hnc
  have hk1 : Real.sqrt (-c) < 1 := by
    have h : Real.sqrt (-c) < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt (le_of_lt hnc) (by linarith)
    rwa [Real.sqrt_one] at h
  have hksq : (Real.sqrt (-c)) ^ 2 = -c := Real.sq_sqrt hnc.le
  have hkne : Real.sqrt (-c) ≠ 0 := hk0.ne'
  have hc_eq : c = -((Real.sqrt (-c)) ^ 2) := by rw [hksq]; ring
  -- Step 0: rewrite integrand globally (ring, no side conditions).
  have e0 : (fun t : ℝ => ((1 : ℝ) + c * t ^ 2)⁻¹)
      = fun t : ℝ => ((1 : ℝ) - (Real.sqrt (-c) * t) ^ 2)⁻¹ := by
    funext t
    congr 1
    conv_lhs => rw [hc_eq]
    ring
  -- Step 1: partial fractions, valid on [0,1] (ae step).
  have hpf : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ((1 : ℝ) - (Real.sqrt (-c) * t) ^ 2)⁻¹
        = (1 / 2) * ((1 - Real.sqrt (-c) * t)⁻¹ + (1 + Real.sqrt (-c) * t)⁻¹) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hkt : Real.sqrt (-c) * t < 1 := by
      calc Real.sqrt (-c) * t ≤ Real.sqrt (-c) * 1 :=
            mul_le_mul_of_nonneg_left ht1 hk0.le
        _ < 1 := by simpa using hk1
    have h1 : (0 : ℝ) < 1 - Real.sqrt (-c) * t := by linarith
    have h2 : (0 : ℝ) < 1 + Real.sqrt (-c) * t := by
      have := mul_pos hk0 ht0; linarith
    have h1ne : (1 : ℝ) - Real.sqrt (-c) * t ≠ 0 := ne_of_gt h1
    have h2ne : (1 : ℝ) + Real.sqrt (-c) * t ≠ 0 := ne_of_gt h2
    have efac : (1 - Real.sqrt (-c) * t) * (1 + Real.sqrt (-c) * t)
        = 1 - (Real.sqrt (-c) * t) ^ 2 := by
      ring
    rw [←efac, mul_inv]
    field_simp
    ring
  have hint1 : IntervalIntegrable (fun t : ℝ => ((1 : ℝ) - Real.sqrt (-c) * t)⁻¹)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · exact (continuous_const.sub
        (continuous_const.mul continuous_id)).continuousOn
    · intro t ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
        have : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)
        rwa [this] at ht
      have hkt : Real.sqrt (-c) * t ≤ Real.sqrt (-c) * 1 :=
        mul_le_mul_of_nonneg_left ht01.2 hk0.le
      have : (0 : ℝ) < 1 - Real.sqrt (-c) * t := by
        have : Real.sqrt (-c) * t < 1 := by linarith [hk1]
        linarith
      exact this.ne'
  have hint2 : IntervalIntegrable (fun t : ℝ => ((1 : ℝ) + Real.sqrt (-c) * t)⁻¹)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · exact (continuous_const.add
        (continuous_const.mul continuous_id)).continuousOn
    · intro t ht
      have hpos : (0 : ℝ) < 1 + Real.sqrt (-c) * t := by
        have hkt : (0 : ℝ) ≤ Real.sqrt (-c) * t := by
          have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
            have : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)
            rwa [this] at ht
          exact mul_nonneg hk0.le ht01.1
        linarith
      exact hpos.ne'
  have hae : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
      ((1 : ℝ) - (Real.sqrt (-c) * t) ^ 2)⁻¹
        = (1 / 2) * ((1 - Real.sqrt (-c) * t)⁻¹ + (1 + Real.sqrt (-c) * t)⁻¹) := by
    filter_upwards with t ht
    have ht01 : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa using ht
    exact hpf t ht01
  have hsplit : (∫ t in (0 : ℝ)..1, ((1 : ℝ) - (Real.sqrt (-c) * t) ^ 2)⁻¹)
      = (1 / 2) * ((∫ t in (0 : ℝ)..1, ((1 : ℝ) - Real.sqrt (-c) * t)⁻¹)
        + (∫ t in (0 : ℝ)..1, ((1 : ℝ) + Real.sqrt (-c) * t)⁻¹)) := by
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hint1 hint2]
  -- Step 2: split, evaluate each piece, recombine.
  have hkIcc : Real.sqrt (-c) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hk0], hk1.le⟩
  -- Piece I+: substitution v = k*t then w = v+1.
  have hIplus : (∫ t in (0 : ℝ)..1, ((1 : ℝ) + Real.sqrt (-c) * t)⁻¹)
      = Real.log (1 + Real.sqrt (-c)) / Real.sqrt (-c) := by
    have eplus : (fun t : ℝ => ((1 : ℝ) + Real.sqrt (-c) * t)⁻¹)
        = fun t : ℝ => ((fun v : ℝ => ((1 : ℝ) + v)⁻¹) (Real.sqrt (-c) * t)) := rfl
    rw [eplus, integral_comp_mul_left (f := fun v : ℝ => ((1 : ℝ) + v)⁻¹) hkne]
    simp only [mul_zero, mul_one]
    have e2 : (fun v : ℝ => ((1 : ℝ) + v)⁻¹)
        = fun v : ℝ => ((fun w : ℝ => w⁻¹) (v + 1)) := by
      funext v
      congr 1
      ring
    rw [e2, integral_comp_add_right]
    have h1k : (0 : ℝ) < 1 + Real.sqrt (-c) := by
      have := hk0; positivity
    rw [zero_add (1 : ℝ), add_comm (Real.sqrt (-c)) 1,
      integral_inv_of_pos (by norm_num) h1k, div_one]
    rw [smul_eq_mul, div_eq_mul_inv]
    ring
  -- Piece I-: substitution v = k*t then w = 1-v.
  have hIminus : (∫ t in (0 : ℝ)..1, ((1 : ℝ) - Real.sqrt (-c) * t)⁻¹)
      = -Real.log (1 - Real.sqrt (-c)) / Real.sqrt (-c) := by
    have eminus : (fun t : ℝ => ((1 : ℝ) - Real.sqrt (-c) * t)⁻¹)
        = fun t : ℝ => ((fun v : ℝ => ((1 : ℝ) - v)⁻¹) (Real.sqrt (-c) * t)) := rfl
    rw [eminus, integral_comp_mul_left (f := fun v : ℝ => ((1 : ℝ) - v)⁻¹) hkne]
    simp only [mul_zero, mul_one]
    have e3 : (fun v : ℝ => ((1 : ℝ) - v)⁻¹)
        = fun v : ℝ => ((fun w : ℝ => w⁻¹) (1 - v)) := rfl
    rw [e3, integral_comp_sub_left]
    simp only [sub_zero]
    have hmk : (0 : ℝ) < 1 - Real.sqrt (-c) := by linarith [hk1]
    rw [integral_inv_of_pos hmk (by norm_num)]
    have hlog : Real.log (1 / (1 - Real.sqrt (-c)))
        = -Real.log (1 - Real.sqrt (-c)) := by
      rw [Real.log_div (by norm_num) (ne_of_gt hmk), Real.log_one, zero_sub]
    rw [hlog, smul_eq_mul, div_eq_mul_inv]
    ring
  -- Recombine via artanh half-log form.
  have hrecomb : (1 / 2 : ℝ)
      * ((-Real.log (1 - Real.sqrt (-c))) / Real.sqrt (-c)
        + Real.log (1 + Real.sqrt (-c)) / Real.sqrt (-c))
      = Real.artanh (Real.sqrt (-c)) / Real.sqrt (-c) := by
    have hk1ne : (1 : ℝ) - Real.sqrt (-c) ≠ 0 := ne_of_gt (by linarith [hk1])
    have hk1nep : (1 : ℝ) + Real.sqrt (-c) ≠ 0 := ne_of_gt (by
      have := hk0; positivity)
    rw [Real.artanh_eq_half_log hkIcc,
      Real.log_div hk1nep hk1ne, div_eq_mul_inv]
    field_simp
    ring
  calc (∫ t in (0 : ℝ)..1, ((1 : ℝ) + c * t ^ 2)⁻¹)
      = (∫ t in (0 : ℝ)..1, ((1 : ℝ) - (Real.sqrt (-c) * t) ^ 2)⁻¹) := by
        congr 1
    _ = (1 / 2) * ((∫ t in (0 : ℝ)..1, ((1 : ℝ) - Real.sqrt (-c) * t)⁻¹)
        + (∫ t in (0 : ℝ)..1, ((1 : ℝ) + Real.sqrt (-c) * t)⁻¹)) := hsplit
    _ = Real.artanh (Real.sqrt (-c)) / Real.sqrt (-c) := by
      rw [hIminus, hIplus, hrecomb]
