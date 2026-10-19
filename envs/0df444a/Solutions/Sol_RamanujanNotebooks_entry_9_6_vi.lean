-- Prove2me | solution 1 for RamanujanNotebooks.entry_9_6_vi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:02:34.760976+00:00
-- url     : https://prove2.me/submissions/8b11ff30-61f6-4239-8825-4069aa39033f

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_dilogCont

namespace RNE9
open RamanujanNotebooks Real Filter Topology Set

noncomputable def φ (s : ℝ) : ℝ := Real.log (1 - s)
noncomputable def g : ℝ → ℝ := dslope φ 0
noncomputable def L (u : ℝ) : ℝ := -∫ s in (0 : ℝ)..u, g s

lemma φ_hasDeriv (s : ℝ) (hs : s < 1) : HasDerivAt φ (-1 / (1 - s)) s := by
  have h := ((hasDerivAt_id s).const_sub 1).log (by simp; linarith)
  have e : φ = fun y => Real.log (1 - y) := rfl
  rw [e]; simpa using h

lemma g_ne {s : ℝ} (hs : s ≠ 0) : g s = Real.log (1 - s) / s := by
  rw [g, dslope_of_ne _ hs, slope_def_field]; simp [φ]

lemma g_zero : g 0 = -1 := by
  rw [g, dslope_same, (φ_hasDeriv 0 (by norm_num)).deriv]; norm_num

lemma g_cont {s : ℝ} (hs : s < 1) : ContinuousAt g s := by
  by_cases h0 : s = 0
  · subst h0; exact continuousAt_dslope_same.mpr (φ_hasDeriv 0 (by norm_num)).differentiableAt
  · exact (continuousAt_dslope_of_ne h0).mpr (φ_hasDeriv s hs).continuousAt

lemma g_contOn : ContinuousOn g (Iio 1) := fun s hs => (g_cont hs).continuousWithinAt

lemma g_ii {u : ℝ} (hu : u < 1) : IntervalIntegrable g MeasureTheory.volume 0 u := by
  apply ContinuousOn.intervalIntegrable
  apply g_contOn.mono
  intro s hs
  rw [Set.mem_uIcc] at hs
  simp only [mem_Iio]
  rcases hs with h | h <;> linarith [h.2]

lemma L_hasDeriv {u : ℝ} (hu : u < 1) : HasDerivAt L (-g u) u := by
  have h := intervalIntegral.integral_hasDerivAt_right (g_ii hu)
    (g_contOn.stronglyMeasurableAtFilter isOpen_Iio u hu) (g_cont hu)
  exact h.neg

lemma L_zero : L 0 = 0 := by simp [L]

lemma real_integral (u : ℝ) (hu : u < 1) :
    ∫ t in (0 : ℝ)..1, Real.log (1 - t * u) / t = ∫ s in (0 : ℝ)..u, g s := by
  by_cases h0 : u = 0
  · subst h0; simp
  have h1 : ∫ t in (0 : ℝ)..1, Real.log (1 - t * u) / t = ∫ t in (0 : ℝ)..1, u * g (u * t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : t ≠ 0 := ht.1.ne'
    rw [g_ne (mul_ne_zero h0 ht0)]
    field_simp
  rw [h1, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ h0]
  simp only [mul_zero, mul_one, smul_eq_mul]
  field_simp

lemma dilog_eq (u : ℝ) (hu : u < 1) : dilogCont (u : ℂ) = ((L u : ℝ) : ℂ) := by
  rw [dilogCont, L, ← real_integral u hu]
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hpos : 0 < 1 - t * u := by
    rcases le_or_gt u 0 with h | h
    · nlinarith [ht.1]
    · nlinarith [ht.2]
  simp only
  push_cast
  rw [← Complex.ofReal_one, ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_log hpos.le]

lemma deriv_zero (w : ℝ) (hw : w < 1) (hw0 : w ≠ 0) (t : ℝ) (ht : t < 1) (htw : t + w < 1) :
    -g (t / (1 - w)) * (1 / (1 - w)) + -g (w / (1 - t)) * (w / (1 - t) ^ 2) - -g t
      - -g (t * w / ((1 - t) * (1 - w))) * (w / ((1 - t) ^ 2 * (1 - w)))
      - (-1 / (1 - t)) * Real.log (1 - w) = 0 := by
  have h1w : 1 - w ≠ 0 := by linarith
  have h1t : 1 - t ≠ 0 := by linarith
  have hp : 0 < 1 - t - w := by linarith
  by_cases ht0 : t = 0
  · subst ht0
    simp only [zero_div, zero_mul, sub_zero, div_one, g_zero]
    rw [g_ne hw0]
    field_simp
    ring
  · have hu1 : t / (1 - w) ≠ 0 := div_ne_zero ht0 h1w
    have hu2 : w / (1 - t) ≠ 0 := div_ne_zero hw0 h1t
    have hu3 : t * w / ((1 - t) * (1 - w)) ≠ 0 := div_ne_zero (mul_ne_zero ht0 hw0) (mul_ne_zero h1t h1w)
    rw [g_ne hu1, g_ne hu2, g_ne hu3, g_ne ht0]
    have e1 : 1 - t / (1 - w) = (1 - t - w) / (1 - w) := by
      rw [eq_div_iff h1w, sub_mul, div_mul_cancel₀ _ h1w]; ring
    have e2 : 1 - w / (1 - t) = (1 - t - w) / (1 - t) := by
      rw [eq_div_iff h1t, sub_mul, div_mul_cancel₀ _ h1t]; ring
    have e3 : 1 - t * w / ((1 - t) * (1 - w)) = (1 - t - w) / ((1 - t) * (1 - w)) := by
      rw [eq_div_iff (mul_ne_zero h1t h1w), sub_mul, div_mul_cancel₀ _ (mul_ne_zero h1t h1w)]; ring
    rw [e1, e2, e3, Real.log_div hp.ne' h1w, Real.log_div hp.ne' h1t,
      Real.log_div hp.ne' (mul_ne_zero h1t h1w), Real.log_mul h1t h1w]
    field_simp
    ring

lemma real_identity (z w : ℝ) (hz : z < 1) (hw : w < 1) (hzw : z + w < 1) :
    L (z / (1 - w)) + L (w / (1 - z)) =
      L z + L w + L (z * w / ((1 - z) * (1 - w))) + Real.log (1 - z) * Real.log (1 - w) := by
  by_cases hw0 : w = 0
  · subst hw0; simp [L_zero]
  set F : ℝ → ℝ := fun t => L (t / (1 - w)) + L (w / (1 - t)) - L t - L w
      - L (t * w / ((1 - t) * (1 - w))) - Real.log (1 - t) * Real.log (1 - w) with hF
  set S : Set ℝ := Iio (min 1 (1 - w)) with hS
  have hmem : ∀ t ∈ S, t < 1 ∧ t + w < 1 := by
    intro t ht
    simp only [hS, mem_Iio, lt_min_iff] at ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hderiv : ∀ t ∈ S, HasDerivAt F
      (-g (t / (1 - w)) * (1 / (1 - w)) + -g (w / (1 - t)) * (w / (1 - t) ^ 2) - -g t
      - -g (t * w / ((1 - t) * (1 - w))) * (w / ((1 - t) ^ 2 * (1 - w)))
      - (-1 / (1 - t)) * Real.log (1 - w)) t := by
    intro t ht
    obtain ⟨ht1, htw⟩ := hmem t ht
    have h1w : 0 < 1 - w := by linarith
    have h1t : 0 < 1 - t := by linarith
    have hp : 0 < 1 - t - w := by linarith
    have hd1 : HasDerivAt (fun t : ℝ => t / (1 - w)) (1 / (1 - w)) t := by
      simpa using (hasDerivAt_id t).div_const (1 - w)
    have hd2 : HasDerivAt (fun t : ℝ => w / (1 - t)) (w / (1 - t) ^ 2) t := by
      have := (hasDerivAt_const t w).div ((hasDerivAt_id t).const_sub 1) h1t.ne'
      exact this.congr_deriv (by first | (simp; field_simp) | simp)
    have hd3 : HasDerivAt (fun t : ℝ => t * w / ((1 - t) * (1 - w))) (w / ((1 - t) ^ 2 * (1 - w))) t := by
      have := ((hasDerivAt_id t).mul_const w).div (((hasDerivAt_id t).const_sub 1).mul_const (1 - w))
        (mul_pos h1t h1w).ne'
      exact this.congr_deriv (by first | (simp; field_simp; ring) | (simp; field_simp) | simp)
    have a1 : t / (1 - w) < 1 := by rw [div_lt_one h1w]; linarith
    have a2 : w / (1 - t) < 1 := by rw [div_lt_one h1t]; linarith
    have a3 : t * w / ((1 - t) * (1 - w)) < 1 := by
      rw [div_lt_one (mul_pos h1t h1w)]; nlinarith
    have k1 := (L_hasDeriv a1).comp t hd1
    have k2 := (L_hasDeriv a2).comp t hd2
    have k3 := L_hasDeriv ht1
    have k4 := (L_hasDeriv a3).comp t hd3
    have k5 := (φ_hasDeriv t ht1).mul_const (Real.log (1 - w))
    have := ((((k1.add k2).sub k3).sub (hasDerivAt_const t (L w))).sub k4).sub k5
    have hfun : F = ((((((L ∘ fun t => t / (1 - w)) + L ∘ fun t => w / (1 - t)) - L) - fun _ => L w) -
        L ∘ fun t => t * w / ((1 - t) * (1 - w))) - fun y => φ y * Real.log (1 - w)) := by
      funext y; simp [hF, φ]
    rw [hfun]; exact this.congr_deriv (by ring)
  have hdiff : DifferentiableOn ℝ F S := fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
  have hd0 : S.EqOn (deriv F) 0 := by
    intro t ht
    obtain ⟨ht1, htw⟩ := hmem t ht
    rw [(hderiv t ht).deriv]
    exact deriv_zero w hw hw0 t ht1 htw
  have hzS : z ∈ S := by simp only [hS, mem_Iio, lt_min_iff]; constructor <;> linarith
  have h0S : (0 : ℝ) ∈ S := by simp only [hS, mem_Iio, lt_min_iff]; constructor <;> linarith
  have hc := isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio _).isPreconnected hdiff hd0 hzS h0S
  have hF0 : F 0 = 0 := by simp [hF, L_zero]
  rw [hF0] at hc
  simp only [hF] at hc
  linarith

theorem main (z w : ℝ) (hz : z < 1) (hw : w < 1) (hzw : z + w < 1) :
    dilogCont ((z / (1 - w) : ℝ) : ℂ) + dilogCont ((w / (1 - z) : ℝ) : ℂ)
      = dilogCont (z : ℂ) + dilogCont (w : ℂ)
        + dilogCont ((z * w / ((1 - z) * (1 - w)) : ℝ) : ℂ)
        + ((Real.log (1 - z) * Real.log (1 - w) : ℝ) : ℂ) := by
  have h1w : 0 < 1 - w := by linarith
  have h1z : 0 < 1 - z := by linarith
  have a1 : z / (1 - w) < 1 := by rw [div_lt_one h1w]; linarith
  have a2 : w / (1 - z) < 1 := by rw [div_lt_one h1z]; linarith
  have a3 : z * w / ((1 - z) * (1 - w)) < 1 := by
    rw [div_lt_one (mul_pos h1z h1w)]; nlinarith
  rw [dilog_eq _ a1, dilog_eq _ a2, dilog_eq _ hz, dilog_eq _ hw, dilog_eq _ a3]
  exact_mod_cast real_identity z w hz hw hzw

end RNE9

open RamanujanNotebooks in
theorem solution (z w : ℝ) (hz : z < 1) (hw : w < 1) (hzw : z + w < 1) :
    dilogCont ((z / (1 - w) : ℝ) : ℂ) + dilogCont ((w / (1 - z) : ℝ) : ℂ)
      = dilogCont (z : ℂ) + dilogCont (w : ℂ)
        + dilogCont ((z * w / ((1 - z) * (1 - w)) : ℝ) : ℂ)
        + ((Real.log (1 - z) * Real.log (1 - w) : ℝ) : ℂ) :=
  RNE9.main z w hz hw hzw
