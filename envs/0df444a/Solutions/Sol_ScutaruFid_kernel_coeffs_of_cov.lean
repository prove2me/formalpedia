-- Prove2me | solution 1 for ScutaruFid.kernel_coeffs_of_cov
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:37:29.082421+00:00
-- url     : https://prove2.me/submissions/636de3c8-aaab-4766-bb61-9eeb5a691f72

import Mathlib

theorem solution (a : ℂ) (b : ℝ) (hab : 0 < a.re + b) :
    let s : ℂ := a + star a + 2 * (b : ℂ)
    let aqq : ℂ := 1 / s
    let app : ℂ := 4 * (a * star a - (b : ℂ) ^ 2) / s
    let apq : ℂ := Complex.I * (a - star a) / s
    let detA : ℂ := aqq * app - apq ^ 2
    aqq.im = 0 ∧ app.im = 0 ∧ apq.im = 0 ∧
      a = (detA + 1) / (4 * aqq) - Complex.I * apq / (2 * aqq) ∧
      (b : ℂ) = -(detA - 1) / (4 * aqq) := by
  intro s aqq app apq detA
  obtain ⟨r, hr⟩ : ∃ r, r = a.re := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = a.im := ⟨_, rfl⟩
  have ha : a = (r : ℂ) + (m : ℂ) * Complex.I := by rw [hr, hm]; exact (Complex.re_add_im a).symm
  have hpos : 0 < r + b := by rw [hr]; exact hab
  have hne : ((r : ℂ) + (b : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hsa : star a = (r : ℂ) - (m : ℂ) * Complex.I := by
    rw [ha]
    apply Complex.ext <;> simp
  have hs : s = ((2 * (r + b) : ℝ) : ℂ) := by
    show a + star a + 2 * (b : ℂ) = _
    rw [hsa, ha]
    push_cast <;> ring
  have haa : a * star a = ((r ^ 2 + m ^ 2 : ℝ) : ℂ) := by
    rw [hsa, ha]
    push_cast
    linear_combination (-(m : ℂ) ^ 2) * hI
  have hamsa : Complex.I * (a - star a) = ((-2 * m : ℝ) : ℂ) := by
    rw [hsa, ha]
    push_cast
    linear_combination (2 * (m : ℂ)) * hI
  have haqq : aqq = ((1 / (2 * (r + b)) : ℝ) : ℂ) := by
    show 1 / s = _
    rw [hs, Complex.ofReal_div, Complex.ofReal_one]
  have happ : app = ((4 * (r ^ 2 + m ^ 2 - b ^ 2) / (2 * (r + b)) : ℝ) : ℂ) := by
    show 4 * (a * star a - (b : ℂ) ^ 2) / s = _
    rw [haa, hs]
    push_cast <;> ring
  have hapq : apq = ((-2 * m / (2 * (r + b)) : ℝ) : ℂ) := by
    show Complex.I * (a - star a) / s = _
    rw [hamsa, hs]
    push_cast <;> ring
  have hdet : detA = (((r - b) / (r + b) : ℝ) : ℂ) := by
    show aqq * app - apq ^ 2 = _
    rw [haqq, happ, hapq]
    push_cast
    field_simp <;> ring
  refine ⟨by rw [haqq, Complex.ofReal_im], by rw [happ, Complex.ofReal_im],
    by rw [hapq, Complex.ofReal_im], ?_, ?_⟩
  · rw [hdet, haqq, hapq, ha]
    push_cast
    field_simp <;> ring
  · rw [hdet, haqq]
    push_cast
    field_simp <;> ring
