-- Prove2me | solution 1 for PriceQualityService.convex_interior_max_const
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:48:04.287286+00:00
-- url     : https://prove2.me/submissions/5cefe89d-5049-49f9-b820-f56494cccba0

import Mathlib

theorem solution {f : ℝ → ℝ} {ts tl t : ℝ}
    (hf : ConvexOn ℝ (Set.Icc ts tl) f) (ht : t ∈ Set.Ioo ts tl)
    (hmax : ∀ t' ∈ Set.Icc ts tl, f t' ≤ f t) :
    ∀ t' ∈ Set.Icc ts tl, f t' = f t := by
  intro t' ht'
  apply le_antisymm (hmax t' ht')
  obtain ⟨h1, h2⟩ := ht
  obtain ⟨h1', h2'⟩ := ht'
  rcases lt_trichotomy t' t with h | h | h
  · have hd : 0 < tl - t' := by linarith
    obtain ⟨a, ha⟩ : ∃ a, a = (tl - t) / (tl - t') := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = (t - t') / (tl - t') := ⟨_, rfl⟩
    have ha0 : 0 < a := by rw [ha]; exact div_pos (by linarith) hd
    have hb0 : 0 ≤ b := by rw [hb]; exact div_nonneg (by linarith) hd.le
    have hab : a + b = 1 := by
      rw [ha, hb, ← add_div, div_eq_one_iff_eq hd.ne']; ring
    have he : a * t' + b * tl = t := by
      rw [ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd.ne']; ring
    have hc := hf.2 ⟨h1', h2'⟩ ⟨by linarith, le_rfl⟩ ha0.le hb0 hab
    simp only [smul_eq_mul] at hc
    rw [he] at hc
    have hm := hmax tl ⟨by linarith, le_rfl⟩
    have hb2 : b * f tl ≤ b * f t := mul_le_mul_of_nonneg_left hm hb0
    have hsplit : a * f t + b * f t = f t := by rw [← add_mul, hab, one_mul]
    have : a * f t ≤ a * f t' := by linarith
    exact le_of_mul_le_mul_left this ha0
  · rw [h]
  · have hd : 0 < t' - ts := by linarith
    obtain ⟨a, ha⟩ : ∃ a, a = (t' - t) / (t' - ts) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = (t - ts) / (t' - ts) := ⟨_, rfl⟩
    have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (by linarith) hd.le
    have hb0 : 0 < b := by rw [hb]; exact div_pos (by linarith) hd
    have hab : a + b = 1 := by
      rw [ha, hb, ← add_div, div_eq_one_iff_eq hd.ne']; ring
    have he : a * ts + b * t' = t := by
      rw [ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd.ne']; ring
    have hc := hf.2 ⟨le_rfl, by linarith⟩ ⟨h1', h2'⟩ ha0 hb0.le hab
    simp only [smul_eq_mul] at hc
    rw [he] at hc
    have hm := hmax ts ⟨le_rfl, by linarith⟩
    have ha2 : a * f ts ≤ a * f t := mul_le_mul_of_nonneg_left hm ha0
    have hsplit : a * f t + b * f t = f t := by rw [← add_mul, hab, one_mul]
    have : b * f t ≤ b * f t' := by linarith
    exact le_of_mul_le_mul_left this hb0
