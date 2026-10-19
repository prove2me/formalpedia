-- Prove2me | solution 1 for ShorNonsmooth.LinearRate.quadratic_cosine_min
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:54:49.708629+00:00
-- url     : https://prove2.me/submissions/b4ead0a4-86b3-4b75-aad8-c3bdbfe41248

import Mathlib
set_option autoImplicit false

lemma qcm_key {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (hA : A.IsSymmetric)
    (lam mu : ℝ) (hlam : lam ≤ mu)
    (hlow : ∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x)
    (hup : ∀ x, inner ℝ (A x) x ≤ mu * ‖x‖ ^ 2) (x : EuclideanSpace ℝ (Fin n)) :
    ‖A x‖ ^ 2 + lam * mu * ‖x‖ ^ 2 ≤ (lam + mu) * inner ℝ (A x) x := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (lam + mu) / 2 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (mu - lam) / 2 := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  -- polarization identity
  have pol : ∀ y : EuclideanSpace ℝ (Fin n),
      4 * inner ℝ (A x - c • x) y =
        (inner ℝ (A (x + y)) (x + y) - c * ‖x + y‖ ^ 2) -
        (inner ℝ (A (x - y)) (x - y) - c * ‖x - y‖ ^ 2) := by
    intro y
    have h1 : inner ℝ (A y) x = inner ℝ (A x) y := by
      rw [hA y x]; exact real_inner_comm _ _
    have h3 : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
    rw [map_add, map_sub, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left]
    rw [h1, h3]
    ring
  have bound : ∀ y : EuclideanSpace ℝ (Fin n),
      inner ℝ (A x - c • x) y ≤ r * (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
    intro y
    have e1 := hup (x + y)
    have e2 := hlow (x - y)
    have p1 := norm_add_sq_real x y
    have p2 := norm_sub_sq_real x y
    have := pol y
    rw [hr]
    nlinarith
  have hN : ‖A x - c • x‖ ≤ r * ‖x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hb : A x - c • x = 0
    · rw [hb]; simp; positivity
    have hm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hNp : 0 < ‖A x - c • x‖ := norm_pos_iff.mpr hb
    have := bound ((‖x‖ / ‖A x - c • x‖) • (A x - c • x))
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hm hNp)] at this
    have e : ‖x‖ / ‖A x - c • x‖ * ‖A x - c • x‖ = ‖x‖ := by field_simp
    have e3 : ‖x‖ / ‖A x - c • x‖ * ‖A x - c • x‖ ^ 2 = ‖x‖ * ‖A x - c • x‖ := by
      field_simp
    rw [e3, e] at this
    have h5 : ‖x‖ * ‖A x - c • x‖ ≤ ‖x‖ * (r * ‖x‖) := by nlinarith
    exact le_of_mul_le_mul_left h5 hm
  have hsq : ‖A x - c • x‖ ^ 2 ≤ r ^ 2 * ‖x‖ ^ 2 := by
    calc ‖A x - c • x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) hN 2
      _ = r ^ 2 * ‖x‖ ^ 2 := by ring
  have hexp : ‖A x - c • x‖ ^ 2 = ‖A x‖ ^ 2 - 2 * c * inner ℝ (A x) x + c ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have h1 : (c ^ 2 - r ^ 2) * ‖x‖ ^ 2 = lam * mu * ‖x‖ ^ 2 := by
    rw [hc, hr]; ring
  have h2c : 2 * c * inner ℝ (A x) x = (lam + mu) * inner ℝ (A x) x := by
    rw [hc]; ring
  nlinarith [h1, h2c, hsq, hexp]

lemma qcm_gen {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (s₁ s₂ : EuclideanSpace ℝ (Fin n)) (hs₁ : ‖s₁‖ = 1) (hs₂ : ‖s₂‖ = 1)
    (hAs₁ : A s₁ = lam • s₁) (hAs₂ : A s₂ = mu • s₂)
    (h0 : inner ℝ s₁ s₂ = (0 : ℝ)) (a b : ℝ)
    (ha2 : a ^ 2 = mu / (lam + mu)) (hb2 : b ^ 2 = lam / (lam + mu)) :
    ‖a • s₁ + b • s₂‖ = 1 ∧
    inner ℝ (A (a • s₁ + b • s₂)) (a • s₁ + b • s₂) = 2 * lam * mu / (lam + mu) ∧
    ‖A (a • s₁ + b • s₂)‖ ^ 2 = lam * mu := by
  have hsum : 0 < lam + mu := by linarith
  have h0' : inner ℝ s₂ s₁ = (0 : ℝ) := by rw [real_inner_comm]; exact h0
  have s11 : inner ℝ s₁ s₁ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hs₁]; norm_num
  have s22 : inner ℝ s₂ s₂ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hs₂]; norm_num
  have hAx : A (a • s₁ + b • s₂) = (a * lam) • s₁ + (b * mu) • s₂ := by
    simp only [map_add, map_smul, hAs₁, hAs₂, smul_smul]
  have hab : a ^ 2 + b ^ 2 = 1 := by rw [ha2, hb2]; field_simp; ring
  have hxx : ‖a • s₁ + b • s₂‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      s11, s22, h0, h0']
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have := Real.sqrt_sq (norm_nonneg (a • s₁ + b • s₂))
    rw [hxx] at this; simpa using this.symm
  · rw [hAx]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      s11, s22, h0, h0']
    have h3 : a ^ 2 * lam + b ^ 2 * mu = 2 * lam * mu / (lam + mu) := by
      rw [ha2, hb2]; field_simp; ring
    nlinarith [h3]
  · rw [← real_inner_self_eq_norm_sq, hAx]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      s11, s22, h0, h0']
    have h3 : a ^ 2 * lam ^ 2 + b ^ 2 * mu ^ 2 = lam * mu := by
      rw [ha2, hb2]; field_simp
    nlinarith [h3]

theorem solution {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (hA : A.IsSymmetric)
    (lam mu : ℝ) (hlam : 0 < lam)
    (hlow : ∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x)
    (hup : ∀ x, inner ℝ (A x) x ≤ mu * ‖x‖ ^ 2)
    (s₁ s₂ : EuclideanSpace ℝ (Fin n)) (hs₁ : ‖s₁‖ = 1) (hs₂ : ‖s₂‖ = 1)
    (hAs₁ : A s₁ = lam • s₁) (hAs₂ : A s₂ = mu • s₂) :
    IsLeast {c : ℝ | ∃ x : EuclideanSpace ℝ (Fin n), x ≠ 0 ∧
        c = inner ℝ (A x) x / (‖A x‖ * ‖x‖)}
      (2 * Real.sqrt (lam * mu) / (lam + mu)) ∧
    (inner ℝ s₁ s₂ = (0 : ℝ) →
      let x := Real.sqrt (mu / (lam + mu)) • s₁ + Real.sqrt (lam / (lam + mu)) • s₂
      inner ℝ (A x) x / (‖A x‖ * ‖x‖) = 2 * Real.sqrt (lam * mu) / (lam + mu)) := by
  have hlm : lam ≤ mu := by
    have := hlow s₂
    rw [hAs₂, real_inner_smul_left, real_inner_self_eq_norm_sq, hs₂] at this
    linarith
  have hmu : 0 < mu := lt_of_lt_of_le hlam hlm
  have hsum : 0 < lam + mu := by linarith
  have hlmpos : 0 < lam * mu := mul_pos hlam hmu
  have hsq : Real.sqrt (lam * mu) ^ 2 = lam * mu := Real.sq_sqrt hlmpos.le
  have hsqpos : 0 < Real.sqrt (lam * mu) := Real.sqrt_pos.mpr hlmpos
  have ha2 : Real.sqrt (mu / (lam + mu)) ^ 2 = mu / (lam + mu) := Real.sq_sqrt (by positivity)
  have hb2 : Real.sqrt (lam / (lam + mu)) ^ 2 = lam / (lam + mu) := Real.sq_sqrt (by positivity)
  have orth : inner ℝ s₁ s₂ = (0 : ℝ) →
      let x := Real.sqrt (mu / (lam + mu)) • s₁ + Real.sqrt (lam / (lam + mu)) • s₂
      inner ℝ (A x) x / (‖A x‖ * ‖x‖) = 2 * Real.sqrt (lam * mu) / (lam + mu) := by
    intro h0 x
    obtain ⟨hxn, hip, hnA⟩ := qcm_gen A lam mu hlam hmu s₁ s₂ hs₁ hs₂ hAs₁ hAs₂ h0 _ _ ha2 hb2
    have hnA' : ‖A x‖ = Real.sqrt (lam * mu) := by
      rw [← hnA]; exact (Real.sqrt_sq (norm_nonneg _)).symm
    rw [hip, hnA', hxn]
    field_simp
    nlinarith [hsq]
  refine ⟨⟨?_, ?_⟩, orth⟩
  · -- attained
    rcases hlm.lt_or_eq with hlt | heq
    · have h0 : inner ℝ s₁ s₂ = (0 : ℝ) := by
        have h1 : lam * inner ℝ s₁ s₂ = mu * inner ℝ s₁ s₂ := by
          have := hA s₁ s₂
          rw [hAs₁, hAs₂, real_inner_smul_left, real_inner_smul_right] at this
          exact this
        have : (mu - lam) * inner ℝ s₁ s₂ = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact h
      obtain ⟨hxn, -, -⟩ := qcm_gen A lam mu hlam hmu s₁ s₂ hs₁ hs₂ hAs₁ hAs₂ h0 _ _ ha2 hb2
      refine ⟨_, ?_, (orth h0).symm⟩
      intro hx0
      rw [hx0] at hxn; simp at hxn
    · subst heq
      refine ⟨s₁, ?_, ?_⟩
      · intro h; rw [h] at hs₁; simp at hs₁
      · rw [hAs₁, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, hs₁,
          Real.norm_eq_abs, abs_of_pos hlam]
        have : Real.sqrt (lam * lam) = lam := Real.sqrt_mul_self hlam.le
        rw [this]
        field_simp
        norm_num
  · -- lower bound
    rintro c ⟨x, hx, rfl⟩
    have hm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hip : 0 < inner ℝ (A x) x := lt_of_lt_of_le (mul_pos hlam (pow_pos hm 2)) (hlow x)
    have hAn : 0 < ‖A x‖ := by
      rcases (norm_nonneg (A x)).lt_or_eq with h | h
      · exact h
      · exfalso
        have : A x = 0 := norm_eq_zero.mp h.symm
        rw [this] at hip; simp at hip
    have key := qcm_key A hA lam mu hlm hlow hup x
    have e : (Real.sqrt (lam * mu) * ‖x‖) ^ 2 = lam * mu * ‖x‖ ^ 2 := by
      rw [mul_pow, hsq]
    have amgm : 2 * Real.sqrt (lam * mu) * (‖A x‖ * ‖x‖) ≤ ‖A x‖ ^ 2 + lam * mu * ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖A x‖ - Real.sqrt (lam * mu) * ‖x‖), e]
    rw [div_le_div_iff₀ hsum (mul_pos hAn hm)]
    linarith
