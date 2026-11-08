-- Prove2me | solution 1 for RankOneBTF.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:18:18.781748+00:00
-- url     : https://prove2.me/submissions/35798d8d-1e94-4fa1-ae72-df03688df8d2

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hm : Measurable X) (hi : Integrable X μ) (hpos : ∀ ω, 0 < X ω)
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ t → μ.real {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤ f t)
    (s : ℝ) (hs : 0 ≤ s) :
    μ.real {ω | s ≤ |1 / X ω - 1 / ∫ ω', X ω' ∂μ|} ≤
      f ((∫ ω, X ω ∂μ) - 1 / (1 / (∫ ω, X ω ∂μ) + s)) := by
  obtain ⟨m, hmd⟩ : ∃ m, m = ∫ ω', X ω' ∂μ := ⟨_, rfl⟩
  rw [← hmd]
  have hmpos : 0 < m := by
    rw [hmd, integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hi]
    have : Function.support X = Set.univ := by
      ext ω; simp [(hpos ω).ne']
    rw [this]; simp
  have hap : 0 < 1 / m := by positivity
  have hd : 0 < 1 / m + s := by linarith
  have ht : 0 ≤ m - 1 / (1 / m + s) := by
    have : 1 / (1 / m + s) ≤ m := by
      rw [div_le_iff₀ hd]
      have : m * (1 / m) = 1 := by field_simp
      nlinarith
    linarith
  refine le_trans ?_ (hf _ ht)
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hx := hpos ω
  rcases le_abs'.mp hω with h | h
  · -- 1/X - 1/m ≤ -s : 1/X ≤ 1/m - s
    have h1 : 1 / X ω ≤ 1 / m - s := by linarith
    have h2 : 0 < 1 / m - s := lt_of_lt_of_le (by positivity) h1
    have h3 : 1 / (1 / m - s) ≤ X ω := by
      rw [div_le_iff₀ h2]
      have : X ω * (1 / X ω) = 1 := by field_simp
      nlinarith
    -- 1/(a-s) - 1/a ≥ 1/a - 1/(a+s)
    have key : m - 1 / (1 / m + s) ≤ 1 / (1 / m - s) - m := by
      have e1 : m = 1 / (1 / m) := by field_simp
      obtain ⟨a, ha⟩ : ∃ a, a = 1 / m := ⟨_, rfl⟩
      rw [← ha] at h2 hd hap ⊢
      rw [e1, ← ha]
      rw [show 1 / a - 1 / (a + s) = s / (a * (a + s)) by field_simp; ring,
        show 1 / (a - s) - 1 / a = s / (a * (a - s)) by field_simp; ring]
      apply div_le_div_of_nonneg_left hs (by positivity)
      nlinarith
    rw [le_abs]; left; linarith
  · have h1 : 1 / m + s ≤ 1 / X ω := by linarith
    have h3 : X ω ≤ 1 / (1 / m + s) := by
      rw [le_div_iff₀ hd]
      have : X ω * (1 / X ω) = 1 := by field_simp
      nlinarith
    rw [le_abs]; right; linarith
