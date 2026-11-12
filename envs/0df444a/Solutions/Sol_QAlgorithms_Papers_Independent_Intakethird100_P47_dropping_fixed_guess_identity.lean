-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P47.dropping_fixed_guess_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:45:51.520901+00:00
-- url     : https://prove2.me/submissions/bcf3d035-8fdf-48c2-90a6-1f9659e3f0b2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

open scoped ComplexConjugate

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P47 in
theorem solution (p0 p1 P0 P1 : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hp : p0 + p1 = 1)
    (hP0 : 0 ≤ P0 ∧ P0 ≤ 1) (hP1 : 0 ≤ P1 ∧ P1 ≤ 1)
    (hu0 : 0 < p0 * P0 + p1 * (1 - P1))
    (hu1 : 0 < p0 * (1 - P0) + p1 * P1) :
    let j := guessLaw p0 p1 P0 P1
    let u0 := aliceMarginal j false
    let u1 := aliceMarginal j true
    let k := balanceRetention j
    IsPairLaw j ∧
    u0 = p0 * P0 + p1 * (1 - P1) ∧ u1 = p0 * (1 - P0) + p1 * P1 ∧
    (∀ A, 0 < k A ∧ k A ≤ 1) ∧
    retention j k = 2 * min u0 u1 ∧ 0 < retention j k ∧
    (∀ A, aliceMarginal (retainedLaw j k) A = 1 / 2) ∧
    (∑ A, retainedLaw j k A A) = (1 / 2) * (p0 * P0 / u0 + p1 * P1 / u1) ∧
    (u0 = u1 → ∀ A, k A = 1) := by
  intro j u0 u1 k
  have e_ff : j false false = p0 * P0 := rfl
  have e_ft : j false true = p1 * (1 - P1) := rfl
  have e_tf : j true false = p0 * (1 - P0) := rfl
  have e_tt : j true true = p1 * P1 := rfl
  have hu0' : u0 = j false true + j false false := by
    show aliceMarginal j false = _
    rw [aliceMarginal, Fintype.sum_bool]
  have hu1' : u1 = j true true + j true false := by
    show aliceMarginal j true = _
    rw [aliceMarginal, Fintype.sum_bool]
  have hU0 : u0 = p0 * P0 + p1 * (1 - P1) := by rw [hu0', e_ft, e_ff]; ring
  have hU1 : u1 = p0 * (1 - P0) + p1 * P1 := by rw [hu1', e_tt, e_tf]; ring
  have hpos0 : 0 < u0 := by rw [hU0]; exact hu0
  have hpos1 : 0 < u1 := by rw [hU1]; exact hu1
  have hm : 0 < min u0 u1 := lt_min hpos0 hpos1
  have hk0 : k false = min u0 u1 / u0 := rfl
  have hk1 : k true = min u0 u1 / u1 := rfl
  have kf : u0 * k false = min u0 u1 := by rw [hk0]; exact mul_div_cancel₀ _ hpos0.ne'
  have kt : u1 * k true = min u0 u1 := by rw [hk1]; exact mul_div_cancel₀ _ hpos1.ne'
  have hret : retention j k = 2 * min u0 u1 := by
    rw [retention, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    linear_combination kt + kf - (k true) * hu1' - (k false) * hu0'
  have hR : (2 * min u0 u1) ≠ 0 := (mul_pos two_pos hm).ne'
  refine ⟨⟨?_, ?_⟩, hU0, hU1, ?_, hret, ?_, ?_, ?_, ?_⟩
  · intro A B
    cases A <;> cases B
    · rw [e_ff]; exact mul_nonneg hp0 hP0.1
    · rw [e_ft]; exact mul_nonneg hp1 (by linarith [hP1.2])
    · rw [e_tf]; exact mul_nonneg hp0 (by linarith [hP0.2])
    · rw [e_tt]; exact mul_nonneg hp1 hP1.1
  · rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, e_tt, e_tf, e_ft, e_ff]
    linarith
  · intro A
    cases A
    · rw [hk0]
      exact ⟨div_pos hm hpos0, (div_le_one hpos0).2 (min_le_left _ _)⟩
    · rw [hk1]
      exact ⟨div_pos hm hpos1, (div_le_one hpos1).2 (min_le_right _ _)⟩
  · rw [hret]; linarith
  · intro A
    cases A
    · rw [aliceMarginal, Fintype.sum_bool]
      simp only [retainedLaw]
      rw [hret, ← add_div, ← add_mul, ← hu0', kf, div_eq_iff hR]
      ring
    · rw [aliceMarginal, Fintype.sum_bool]
      simp only [retainedLaw]
      rw [hret, ← add_div, ← add_mul, ← hu1', kt, div_eq_iff hR]
      ring
  · rw [Fintype.sum_bool]
    simp only [retainedLaw]
    rw [hret, e_tt, e_ff, hk1, hk0]
    have h0 := hpos0.ne'
    have h1 := hpos1.ne'
    have h2 := hm.ne'
    field_simp <;> ring
  · intro h A
    cases A
    · rw [hk0, ← h, min_self, div_self hpos0.ne']
    · rw [hk1, h, min_self, div_self hpos1.ne']
