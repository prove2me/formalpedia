-- Prove2me | solution 1 for RouzeFranca.LearnGibbs.abs_trace_le_lip_mul_W1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:18:57.579192+00:00
-- url     : https://prove2.me/submissions/d36b993e-aac4-4ff2-99bc-4db48fe971d1

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs
import Definitions.Def_RouzeFranca_LearnGibbs_W1Le
import Definitions.Def_RouzeFranca_LearnGibbs_IsLipSeminorm

open Matrix

open RouzeFranca.LearnGibbs in
theorem solution {n : ℕ} (lip : Mat n → ℝ) (hlip : IsLipSeminorm lip)
    (ρ σ : Mat n) (w : ℝ) (hW : W1Le lip ρ σ w) (X : Mat n) (hX : X.IsHermitian) :
    |(trace (X * (ρ - σ))).re| ≤ lip X * w := by
  obtain ⟨hnn, hhom⟩ := hlip
  have key : ∀ c : ℝ, lip ((c : ℂ) • X) ≤ 1 → |c| * |(trace (X * (ρ - σ))).re| ≤ w := by
    intro c hc
    have h := hW ((c : ℂ) • X) (hX.smul (Complex.conj_ofReal c)) hc
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, abs_mul] at h
    exact h
  rcases eq_or_lt_of_le (hnn X) with h0 | hpos
  · have ht0 : (trace (X * (ρ - σ))).re = 0 := by
      by_contra hne
      have htp : 0 < |(trace (X * (ρ - σ))).re| := abs_pos.mpr hne
      have hw0 : 0 ≤ w := by
        have := key 0 (by rw [hhom, ← h0, mul_zero]; norm_num)
        rw [abs_zero, zero_mul] at this
        exact this
      have := key ((w + 1) / |(trace (X * (ρ - σ))).re|) (by rw [hhom, ← h0, mul_zero]; norm_num)
      rw [abs_of_pos (div_pos (by linarith) htp), div_mul_cancel₀ _ htp.ne'] at this
      linarith
    rw [ht0, abs_zero, ← h0, zero_mul]
  · have := key (1 / lip X)
      (by rw [hhom, abs_of_pos (one_div_pos.mpr hpos), one_div_mul_cancel hpos.ne'])
    rw [abs_of_pos (one_div_pos.mpr hpos), div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos] at this
    linarith [mul_comm w (lip X)]
