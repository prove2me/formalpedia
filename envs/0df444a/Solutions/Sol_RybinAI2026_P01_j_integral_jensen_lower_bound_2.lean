-- Prove2me | solution 2 for RybinAI2026.P01.j_integral_jensen_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T03:19:13.298063+00:00
-- url     : https://prove2.me/submissions/95cfe736-808e-4b43-b760-c636b7870aa7

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (3 : ℝ) / (2 * a + b) ≤ ∫ t in (0 : ℝ)..1, (a + (b - a) * t ^ 2)⁻¹ := by
  set m : ℝ := (2 * a + b) / 3 with hm
  have hmpos : 0 < m := by linarith
  have hm2pos : (0 : ℝ) < m ^ 2 := pow_pos hmpos 2
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le (by norm_num)
  have hcontD : Continuous fun t : ℝ => a + (b - a) * t ^ 2 := by continuity
  have hcontP : Continuous fun t : ℝ => (b - a) * t ^ 2 := by continuity
  have hcontC : Continuous fun _ : ℝ => a := continuous_const
  have hcont2m : Continuous fun _ : ℝ => (2 * m) := continuous_const
  have hcontBmD : Continuous fun t : ℝ => 2 * m - (a + (b - a) * t ^ 2) := by continuity
  have hcontB : Continuous fun t : ℝ => (2 * m - (a + (b - a) * t ^ 2)) / m ^ 2 := by continuity
  have hcontI : ContinuousOn (fun t : ℝ => (a + (b - a) * t ^ 2)⁻¹) (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀ hcontD.continuousOn
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have ht2nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    have ht2le : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1, sq_nonneg t]
    have hpos : (0 : ℝ) < a + (b - a) * t ^ 2 := by
      rcases le_total a b with hab | hab
      · have h1 : (0 : ℝ) ≤ (b - a) * t ^ 2 :=
          mul_nonneg (sub_nonneg.mpr hab) ht2nn
        linarith
      · have hneg : b - a ≤ 0 := sub_nonpos.mpr hab
        have h2 : (0 : ℝ) ≤ (b - a) * (t ^ 2 - 1) := by
          have hnn2 : (0 : ℝ) ≤ -(b - a) := by linarith [hneg]
          have hcc : (0 : ℝ) ≤ (-(b - a)) * (1 - t ^ 2) :=
            mul_nonneg hnn2 (sub_nonneg.mpr ht2le)
          linarith
        nlinarith [hb, h2]
    exact ne_of_gt hpos
  have hden : ∀ t ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < a + (b - a) * t ^ 2 := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have ht2nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    have ht2le : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1, sq_nonneg t]
    rcases le_total a b with hab | hab
    · have h1 : (0 : ℝ) ≤ (b - a) * t ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hab) ht2nn
      linarith
    · have hneg : b - a ≤ 0 := sub_nonpos.mpr hab
      have h2 : (0 : ℝ) ≤ (b - a) * (t ^ 2 - 1) := by
        have hnn2 : (0 : ℝ) ≤ -(b - a) := by linarith [hneg]
        have hcc : (0 : ℝ) ≤ (-(b - a)) * (1 - t ^ 2) :=
          mul_nonneg hnn2 (sub_nonneg.mpr ht2le)
        linarith
      nlinarith [hb, h2]
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (2 * m - (a + (b - a) * t ^ 2)) / m ^ 2 ≤ (a + (b - a) * t ^ 2)⁻¹ := by
    intro t ht
    have hd := hden t ht
    rw [div_le_iff₀ hm2pos, inv_mul_eq_div, le_div_iff₀ hd]
    nlinarith [sq_nonneg (m - (a + (b - a) * t ^ 2))]
  have hintD : IntervalIntegrable (fun t : ℝ => a + (b - a) * t ^ 2) volume (0 : ℝ) 1 :=
    hcontD.intervalIntegrable 0 1
  have hintP : IntervalIntegrable (fun t : ℝ => (b - a) * t ^ 2) volume (0 : ℝ) 1 :=
    hcontP.intervalIntegrable 0 1
  have hintC : IntervalIntegrable (fun _ : ℝ => a) volume (0 : ℝ) 1 :=
    hcontC.intervalIntegrable 0 1
  have hint2m : IntervalIntegrable (fun _ : ℝ => (2 * m)) volume (0 : ℝ) 1 :=
    hcont2m.intervalIntegrable 0 1
  have hintBmD : IntervalIntegrable (fun t : ℝ => 2 * m - (a + (b - a) * t ^ 2))
      volume (0 : ℝ) 1 :=
    hcontBmD.intervalIntegrable 0 1
  have hintB : IntervalIntegrable (fun t : ℝ => (2 * m - (a + (b - a) * t ^ 2)) / m ^ 2)
      volume (0 : ℝ) 1 :=
    hcontB.intervalIntegrable 0 1
  have hcontIu : ContinuousOn (fun t : ℝ => (a + (b - a) * t ^ 2)⁻¹) (Set.uIcc (0 : ℝ) 1) := by
    rw [huIcc]
    exact hcontI
  have hintI : IntervalIntegrable (fun t : ℝ => (a + (b - a) * t ^ 2)⁻¹) volume (0 : ℝ) 1 :=
    hcontIu.intervalIntegrable
  have hpow : ∫ t in (0 : ℝ)..1, t ^ 2 = 1 / 3 := by
    rw [integral_pow]
    all_goals norm_num
  have h3 : ∫ t in (0 : ℝ)..1, (a + (b - a) * t ^ 2) = (2 * a + b) / 3 := by
    have e1 : (∫ t in (0 : ℝ)..1, (a + (b - a) * t ^ 2))
        = (∫ _ in (0 : ℝ)..1, a) + (∫ t in (0 : ℝ)..1, (b - a) * t ^ 2) :=
      intervalIntegral.integral_add hintC hintP
    have e2 : (∫ t in (0 : ℝ)..1, (b - a) * t ^ 2) = (b - a) * (1 / 3) := by
      rw [intervalIntegral.integral_const_mul, hpow]
    rw [e1, intervalIntegral.integral_const, e2]
    simp only [smul_eq_mul, sub_zero, mul_one]
    ring
  have havg : ∫ t in (0 : ℝ)..1, (2 * m - (a + (b - a) * t ^ 2)) / m ^ 2
      = (3 : ℝ) / (2 * a + b) := by
    have e1 : (∫ t in (0 : ℝ)..1, (2 * m - (a + (b - a) * t ^ 2)) / m ^ 2)
        = (((∫ _ in (0 : ℝ)..1, (2 * m)) - (∫ t in (0 : ℝ)..1, (a + (b - a) * t ^ 2))) / m ^ 2) := by
      have hmul : ∀ t : ℝ, (2 * m - (a + (b - a) * t ^ 2)) / m ^ 2
          = (2 * m - (a + (b - a) * t ^ 2)) * (m ^ 2)⁻¹ := fun t => div_eq_mul_inv _ _
      simp only [hmul]
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub hint2m hintD,
        ← div_eq_mul_inv]
    rw [e1, intervalIntegral.integral_const, h3]
    rw [hm]
    simp only [smul_eq_mul, sub_zero, mul_one]
    field_simp
    ring
  rw [← havg]
  exact intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hintB hintI hpt
