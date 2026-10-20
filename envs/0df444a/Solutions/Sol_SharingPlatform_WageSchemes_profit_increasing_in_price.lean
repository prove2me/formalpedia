-- Prove2me | solution 1 for SharingPlatform.WageSchemes.profit_increasing_in_price
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:36:58.28982+00:00
-- url     : https://prove2.me/submissions/122c673f-54ba-448d-b957-1495b097ccdb

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

open SharingPlatform.WageSchemes

theorem solution (P : Params) (hP : P.Standing) :
    StrictMonoOn (profitAtPrice P) (Set.Iic (pHat P)) ∧
    pD P < pHat P ∧ pW P < pHat P ∧
    ∀ α : ℝ, α ∈ Set.Ioo (alphaBar P) 1 → fFCR P α = 0 → priceFCR P α < pHat P := by
  obtain ⟨a, b, c, k, l, m⟩ := P
  obtain ⟨ha, hb, hc, hk, hl, hm, hA1, hA2⟩ := hP
  dsimp only at ha hb hc hk hl hm hA1 hA2
  have ham : 0 < a * m - c * k := by
    rw [div_lt_div_iff₀ hm hc] at hA1; linarith
  have hHat : 2 * c * (m + c) * pHat ⟨a, b, c, k, l, m⟩ = (m + c) * a + c * (a + k) := by
    simp only [pHat]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    simp only [Set.mem_Iic] at hp hq
    have key : profitAtPrice ⟨a, b, c, k, l, m⟩ q - profitAtPrice ⟨a, b, c, k, l, m⟩ p =
        (q - p) * ((m + c) * a + c * (a + k) - c * (m + c) * (p + q)) / m := by
      simp only [profitAtPrice]; field_simp; ring
    have h2 : 0 < (m + c) * a + c * (a + k) - c * (m + c) * (p + q) := by
      have hcm : 0 < c * (m + c) := by positivity
      nlinarith
    have : 0 < (q - p) * ((m + c) * a + c * (a + k) - c * (m + c) * (p + q)) / m :=
      div_pos (mul_pos (by linarith) h2) hm
    linarith
  · simp only [pHat, pD]
    rw [← sub_pos]
    have e : ((m + c) * a + c * (a + k)) / (2 * c * (m + c)) -
        (k * (b + c) * (l + m) + a * (m * (l + m) + (b + c) * (l + 2 * m))) /
          (c * (b + c) * (l + 2 * m) + m * (b + 2 * c) * (l + m)) =
        (a * m - c * k) * (b * c * l + b * l * m + b * m ^ 2 + c ^ 2 * l) /
          (2 * c * (c + m) * (b * c * l + 2 * b * c * m + b * l * m + b * m ^ 2 + c ^ 2 * l +
            2 * c ^ 2 * m + 2 * c * l * m + 2 * c * m ^ 2)) := by
      rw [eq_div_iff (by positivity)]
      field_simp
      ring
    rw [e]; positivity
  · simp only [pHat, pW, wW]
    rw [← sub_pos]
    have e : ((m + c) * a + c * (a + k)) / (2 * c * (m + c)) -
        (a + k - m * ((b * (2 * a * (l + m) + 2 * c * k + k * (2 * l + 3 * m)) +
            c * ((a + 2 * k) * (l + m) + c * k)) /
          (b * (2 * c * (l + 2 * m) + m * (2 * l + 3 * m)) +
            c * (c * (l + 2 * m) + 2 * m * (l + m))))) / c =
        (a * m - c * k) * (2 * b * c * l + 2 * b * l * m + b * m ^ 2 + c ^ 2 * l) /
          (2 * c * (c + m) * (2 * b * c * l + 4 * b * c * m + 2 * b * l * m + 3 * b * m ^ 2 +
            c ^ 2 * l + 2 * c ^ 2 * m + 2 * c * l * m + 2 * c * m ^ 2)) := by
      rw [eq_div_iff (by positivity)]
      field_simp
      ring
    rw [e]; positivity
  · intro α hα hf
    have hα1 : α < 1 := hα.2
    set A := m * (a + k) * (b + c) * (2 * l + m) +
      a * m * (m * (b + 2 * l + m) + c * (l + m)) with hA
    have hApos : 0 < A := by positivity
    have hS : 0 < 2 * a * c + a * m + c * k := by positivity
    set α₀ := 1 - c * (m * a + 2 * m * k + c * k) / (m * (2 * a * c + a * m + c * k)) with hα₀
    have hF1 : fFCR ⟨a, b, c, k, l, m⟩ 1 = -c * (2*a*b*l + 2*a*b*m + a*c*l + a*c*m + 2*b*c*k +
        2*b*k*l + 3*b*k*m + c^2*k + 2*c*k*l + 2*c*k*m) := by
      simp only [fFCR]; ring
    have hF1neg : fFCR ⟨a, b, c, k, l, m⟩ 1 < 0 := by
      rw [hF1]
      have : 0 < c * (2*a*b*l + 2*a*b*m + a*c*l + a*c*m + 2*b*c*k +
        2*b*k*l + 3*b*k*m + c^2*k + 2*c*k*l + 2*c*k*m) := by positivity
      linarith
    have hF0 : fFCR ⟨a, b, c, k, l, m⟩ α₀ = -(2 * c * (a + k) ^ 2 * (c + m) * (a * m - c * k) *
        (2 * b * c * l + 2 * b * l * m + b * m ^ 2 + c ^ 2 * l)) /
          (m * (2 * a * c + a * m + c * k) ^ 2) := by
      rw [eq_div_iff (by positivity), hα₀]
      simp only [fFCR]
      field_simp
      ring
    have hF0neg : fFCR ⟨a, b, c, k, l, m⟩ α₀ < 0 := by
      rw [hF0]
      apply div_neg_of_neg_of_pos _ (by positivity)
      have : 0 < 2 * c * (a + k) ^ 2 * (c + m) * (a * m - c * k) *
        (2 * b * c * l + 2 * b * l * m + b * m ^ 2 + c ^ 2 * l) := by positivity
      linarith
    have hα₀1 : α₀ < 1 := by
      have : 0 < c * (m * a + 2 * m * k + c * k) / (m * (2 * a * c + a * m + c * k)) := by
        positivity
      linarith
    -- interpolation identity for the quadratic
    have interp : (1 - α₀) * fFCR ⟨a, b, c, k, l, m⟩ α =
        (1 - α) * fFCR ⟨a, b, c, k, l, m⟩ α₀ + (α - α₀) * fFCR ⟨a, b, c, k, l, m⟩ 1 +
          A * (α - α₀) * (α - 1) * (1 - α₀) := by
      simp only [fFCR, hA]; ring
    have hlt : α < α₀ := by
      by_contra hcon
      push_neg at hcon
      rw [hf, mul_zero] at interp
      have t1 : (1 - α) * fFCR ⟨a, b, c, k, l, m⟩ α₀ < 0 :=
        mul_neg_of_pos_of_neg (by linarith) hF0neg
      have t2 : (α - α₀) * fFCR ⟨a, b, c, k, l, m⟩ 1 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hF1neg.le
      have t3 : A * (α - α₀) * (α - 1) * (1 - α₀) ≤ 0 := by
        have : A * (α - α₀) * (1 - α) * (1 - α₀) ≥ 0 := by
          have := mul_nonneg (mul_nonneg (mul_nonneg hApos.le (sub_nonneg.2 hcon))
            (sub_nonneg.2 hα1.le)) (sub_nonneg.2 hα₀1.le)
          linarith
        nlinarith
      linarith
    -- c + m(1 - α₀) gives exactly pHat
    have hden0 : 0 < c + m * (1 - α₀) := by
      have : 0 < m * (1 - α₀) := mul_pos hm (by linarith)
      linarith
    have hden : c + m * (1 - α₀) < c + m * (1 - α) := by
      have := mul_lt_mul_of_pos_left (show 1 - α₀ < 1 - α by linarith) hm
      linarith
    have hpHat : pHat ⟨a, b, c, k, l, m⟩ = (a + k) / (c + m * (1 - α₀)) := by
      rw [eq_div_iff hden0.ne', hα₀]
      simp only [pHat]
      field_simp
      ring
    simp only [priceFCR]
    rw [hpHat]
    exact div_lt_div_of_pos_left (by linarith) hden0 hden
