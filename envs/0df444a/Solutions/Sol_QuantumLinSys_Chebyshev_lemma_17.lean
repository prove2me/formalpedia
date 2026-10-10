-- Prove2me | solution 1 for QuantumLinSys.Chebyshev.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-09T21:55:50.236985+00:00
-- url     : https://prove2.me/submissions/07ae56e5-9062-435e-8326-07ca3393c2d0

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting

open QuantumLinSys.Chebyshev

theorem solution (κ ε : ℝ) (d b : ℕ) (hκ : 1 ≤ κ) (hd : 1 ≤ d) (hε : 0 < ε)
    (hb : (κ * d) ^ 2 * Real.log (κ * d / ε) ≤ b) :
    ∀ x ∈ Dκ (κ * d), |fTamed b x - 1 / x| ≤ ε := by
  intro x hx
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK1 : 1 ≤ κ * d := by nlinarith
  have hKpos : 0 < κ * d := by linarith
  -- bounds on x
  have hx2 : 1 / (κ * d) ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 ∧ x ≠ 0 := by
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hneg : -1 / (κ * d) < 0 := by
        rw [neg_div]; exact neg_neg_of_pos (by positivity)
      have hxneg : x < 0 := by linarith
      refine ⟨?_, ?_, hxneg.ne⟩
      · have h2' : 1 / (κ * d) ≤ -x := by rw [neg_div] at h2; linarith
        have h0 : 0 ≤ 1 / (κ * d) := by positivity
        calc 1 / (κ * d) ^ 2 = (1 / (κ * d)) ^ 2 := by rw [div_pow, one_pow]
          _ ≤ (-x) ^ 2 := by gcongr
          _ = x ^ 2 := by ring
      · nlinarith
    · have hxpos : 0 < x := lt_of_lt_of_le (by positivity) h1
      refine ⟨?_, ?_, hxpos.ne'⟩
      · calc 1 / (κ * d) ^ 2 = (1 / (κ * d)) ^ 2 := by rw [div_pow, one_pow]
          _ ≤ x ^ 2 := by gcongr
      · nlinarith
  obtain ⟨hlo, hhi, hx0⟩ := hx2
  have hdiff : fTamed b x - 1 / x = -((1 - x ^ 2) ^ b / x) := by
    unfold fTamed; field_simp; ring
  rw [hdiff, abs_neg, abs_div]
  have habsx : 1 / (κ * d) ≤ |x| := by
    by_contra h
    push Not at h
    have h' : |x| ^ 2 < (1 / (κ * d)) ^ 2 := by
      exact pow_lt_pow_left₀ h (abs_nonneg x) (by norm_num)
    rw [sq_abs, div_pow, one_pow] at h'
    linarith
  have h1 : 0 ≤ 1 - x ^ 2 := by linarith
  have hKinv : 1 / (κ * d) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have h2 : 1 - x ^ 2 ≤ 1 - 1 / (κ * d) ^ 2 := by linarith
  have h2' : 0 ≤ 1 - 1 / (κ * d) ^ 2 := by linarith
  rw [abs_of_nonneg (pow_nonneg h1 b)]
  have hexp1 : 1 - 1 / (κ * d) ^ 2 ≤ Real.exp (-(1 / (κ * d) ^ 2)) := by
    have := Real.add_one_le_exp (-(1 / (κ * d) ^ 2)); linarith
  have hlog : Real.log (κ * d / ε) ≤ (b : ℝ) / (κ * d) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hexp2 : Real.exp (-((b : ℝ) / (κ * d) ^ 2)) ≤ ε / (κ * d) := by
    calc Real.exp (-((b : ℝ) / (κ * d) ^ 2)) ≤ Real.exp (-Real.log (κ * d / ε)) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = ε / (κ * d) := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
  calc (1 - x ^ 2) ^ b / |x| ≤ (1 - 1 / (κ * d) ^ 2) ^ b / (1 / (κ * d)) := by
        apply div_le_div₀ (pow_nonneg h2' b) (pow_le_pow_left₀ h1 h2 b) (by positivity) habsx
    _ = κ * d * (1 - 1 / (κ * d) ^ 2) ^ b := by field_simp
    _ ≤ κ * d * Real.exp (-(1 / (κ * d) ^ 2)) ^ b := by gcongr
    _ = κ * d * Real.exp (-((b : ℝ) / (κ * d) ^ 2)) := by
        rw [← Real.exp_nat_mul]; congr 1; ring_nf
    _ ≤ κ * d * (ε / (κ * d)) := by gcongr
    _ = ε := by field_simp

