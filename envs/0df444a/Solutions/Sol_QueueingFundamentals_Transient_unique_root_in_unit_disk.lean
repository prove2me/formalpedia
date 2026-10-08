-- Prove2me | solution 1 for QueueingFundamentals.Transient.unique_root_in_unit_disk
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:26:46.849978+00:00
-- url     : https://prove2.me/submissions/d4e94a42-c09c-44d4-9dbb-b32c6c1383f3

import Mathlib

set_option maxHeartbeats 1000000 in
theorem solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    ‖((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ))‖
        < ‖((lam : ℂ) + (mu : ℂ) + s + r) / (2 * (lam : ℂ))‖ ∧
      {z : ℂ | ‖z‖ < 1 ∧ ((lam : ℂ) + (mu : ℂ) + s) * z - (mu : ℂ) - (lam : ℂ) * z ^ 2 = 0}
        = {((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ))} := by
  set a : ℂ := (lam : ℂ) + (mu : ℂ) + s with ha
  have hx : a.re = lam + mu + s.re := by simp [ha]
  have hy : a.im = s.im := by simp [ha]
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  norm_num at h1 h2
  rw [hx, hy] at h1 h2
  set x := lam + mu + s.re with hxdef
  set y := s.im
  set p := r.re
  set q := r.im
  have hA : ‖a - r‖ ^ 2 = (x - p) ^ 2 + (y - q) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hx, hy]; ring
  have hB : ‖a + r‖ ^ 2 = (x + p) ^ 2 + (y + q) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, hx, hy]; ring
  have hxpos : lam + mu < x := by rw [hxdef]; linarith
  have hD : 0 < x * p + y * q := by
    have e : p * (x * p + y * q) = x * (p ^ 2 + y ^ 2) := by linear_combination (y / 2) * h2
    have : 0 < x * (p ^ 2 + y ^ 2) := by
      have : 0 < x := by linarith
      positivity
    rw [← e] at this
    exact pos_of_mul_pos_right this hr_re.le
  have hx2 : (lam + mu) ^ 2 < x ^ 2 := by
    have : 0 < lam + mu := by linarith
    nlinarith
  have hpq : p ^ 2 + q ^ 2 = x ^ 2 - y ^ 2 - 4 * lam * mu + 2 * q ^ 2 := by
    linear_combination h1
  have hS : 2 * (lam ^ 2 + mu ^ 2) < x ^ 2 + y ^ 2 + p ^ 2 + q ^ 2 := by
    nlinarith [sq_nonneg q]
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (x - p) ^ 2 + (y - q) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = (x + p) ^ 2 + (y + q) ^ 2 := ⟨_, rfl⟩
  have hAB : A * B = 16 * lam ^ 2 * mu ^ 2 := by
    have : A * B = (x ^ 2 - y ^ 2 - p ^ 2 + q ^ 2) ^ 2 + (2 * x * y - 2 * p * q) ^ 2 := by
      rw [hAdef, hBdef]; ring
    rw [this]
    have e1 : x ^ 2 - y ^ 2 - p ^ 2 + q ^ 2 = 4 * lam * mu := by linear_combination -h1
    have e2 : 2 * x * y - 2 * p * q = 0 := by linear_combination -h2
    rw [e1, e2]; ring
  have hlt : A < B := by
    have : B - A = 4 * (x * p + y * q) := by rw [hAdef, hBdef]; ring
    linarith
  have hsum : A + B = 2 * (x ^ 2 + y ^ 2 + p ^ 2 + q ^ 2) := by rw [hAdef, hBdef]; ring
  have hprod : (A - 4 * lam ^ 2) * (B - 4 * lam ^ 2) < 0 := by
    have : (A - 4 * lam ^ 2) * (B - 4 * lam ^ 2)
        = A * B - 4 * lam ^ 2 * (A + B) + 16 * lam ^ 4 := by ring
    rw [this, hAB, hsum]
    have : 0 < lam ^ 2 := by positivity
    linarith [mul_lt_mul_of_pos_left hS this]
  have hAlt : A < 4 * lam ^ 2 := by
    by_contra hc
    push_neg at hc
    have := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr (hc.trans hlt.le))
    linarith
  have hBgt : 4 * lam ^ 2 < B := by
    by_contra hc
    push_neg at hc
    have := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hlt.le.trans hc)) (sub_nonpos.mpr hc)
    linarith
  rw [← hAdef] at hA
  rw [← hBdef] at hB
  have n2l : ‖(2 * (lam : ℂ))‖ = 2 * lam := by
    rw [show (2 * (lam : ℂ)) = ((2 * lam : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hAn : ‖a - r‖ < 2 * lam := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul hc hc (by linarith) (norm_nonneg _)
    nlinarith
  have hBn : 2 * lam < ‖a + r‖ := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul hc hc (norm_nonneg _) (by linarith)
    nlinarith
  have hz1 : ‖(a - r) / (2 * (lam : ℂ))‖ < 1 := by
    rw [norm_div, n2l, div_lt_one (by linarith)]; exact hAn
  have hz2 : 1 < ‖(a + r) / (2 * (lam : ℂ))‖ := by
    rw [norm_div, n2l, one_lt_div (by linarith)]; exact hBn
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hinv : (2 * (lam : ℂ)) * (2 * (lam : ℂ))⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero two_ne_zero hlamC)
  have fact : ∀ z : ℂ, (lam : ℂ) * ((z - (a - r) / (2 * (lam : ℂ))) * (z - (a + r) / (2 * (lam : ℂ))))
      = -(a * z - (mu : ℂ) - (lam : ℂ) * z ^ 2) := by
    intro z
    simp only [div_eq_mul_inv]
    linear_combination (-a * z + (mu : ℂ) * (2 * (lam : ℂ) * (2 * (lam : ℂ))⁻¹ + 1)) * hinv
      + (-(lam : ℂ) * ((2 * (lam : ℂ))⁻¹) ^ 2) * hr
  refine ⟨by linarith, ?_⟩
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hq⟩
    have h := fact z
    rw [hq, neg_zero] at h
    rcases mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hlamC) with h3 | h3
    · exact sub_eq_zero.mp h3
    · exfalso
      rw [sub_eq_zero.mp h3] at hz
      linarith
  · rintro rfl
    refine ⟨hz1, ?_⟩
    have h := fact ((a - r) / (2 * (lam : ℂ)))
    rw [sub_self, zero_mul, mul_zero] at h
    exact neg_eq_zero.mp h.symm
