-- Prove2me | solution 1 for PegProtect.Equilibrium.equation_3_9
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:37:12.808724+00:00
-- url     : https://prove2.me/submissions/e8c63606-a87f-4673-9d23-6b17c21470af

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model
open PegProtect.Equilibrium

theorem solution(P : Params) (hP : P.Standing) (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) :
    piP P ω = piM P ω ↔ ω = (P.phi - P.d - P.beta⁻¹ * (P.phi - 1)) / (1 - P.d) := by
  obtain ⟨hc, hd0, hd1, hphi, hδ, hρ, hν⟩ := hP
  have hq0 : ∀ n : ℕ, q ω (n : ℤ) = (1 - ω) / (1 + ω) * ω ^ n := by
    intro n; unfold q; rw [Int.natAbs_natCast]
  have hq1 : ∀ n : ℕ, q ω (-((n : ℤ) + 1)) = (1 - ω) / (1 + ω) * ω * ω ^ n := by
    intro n; unfold q; rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega]; ring
  have hS0 : ∑' n : ℕ, q ω (n : ℤ) = 1 / (1 + ω) := by
    simp only [hq0]; rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
    have : (1 - ω) ≠ 0 := by linarith
    have : (1 + ω) ≠ 0 := by linarith
    field_simp
  have hS1 : ∑' n : ℕ, q ω (-((n : ℤ) + 1)) = ω / (1 + ω) := by
    simp only [hq1]; rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
    have : (1 - ω) ≠ 0 := by linarith
    have : (1 + ω) ≠ 0 := by linarith
    field_simp
  have hb0 : 0 < P.beta := by unfold Params.beta; positivity
  have hb1 : P.beta < 1 := by
    unfold Params.beta; rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by have := div_pos hδ hρ; linarith)
  have hwb0 : 0 ≤ ω * P.beta := mul_nonneg h0 hb0.le
  have hwb1 : ω * P.beta < 1 := by nlinarith
  have hS2 : ∑' n : ℕ, q ω (n : ℤ) * P.beta ^ (n + 1) = (1 - ω) / (1 + ω) * P.beta / (1 - P.beta * ω) := by
    have : ∀ n : ℕ, q ω (n : ℤ) * P.beta ^ (n + 1) = (1 - ω) / (1 + ω) * P.beta * (ω * P.beta) ^ n := by
      intro n; rw [hq0, mul_pow, pow_succ]; ring
    simp only [this]; rw [tsum_mul_left, tsum_geometric_of_lt_one hwb0 hwb1]
    have : (1 - ω * P.beta) ≠ 0 := by linarith
    have : (1 - P.beta * ω) ≠ 0 := by linarith
    have : (1 + ω) ≠ 0 := by linarith
    field_simp
  have hP' : piP P ω = (P.phi - P.d) / (1 + ω) * (ω + P.beta * (1 - ω) / (1 - P.beta * ω)) := by
    unfold piP; rw [hS1, hS2]
    have : (1 - P.beta * ω) ≠ 0 := by linarith
    have : (1 + ω) ≠ 0 := by linarith
    field_simp
  have hM' : piM P ω = (P.phi - P.d) / (1 + ω) * ω + (P.phi - 1) / (1 + ω) := by
    unfold piM; rw [hS1, hS0]; ring
  have hden : (1 + ω) * (1 - P.beta * ω) ≠ 0 := by
    apply mul_ne_zero <;> linarith
  have key : piP P ω - piM P ω = P.beta * (1 - P.d) * ((P.phi - P.d - P.beta⁻¹ * (P.phi - 1)) / (1 - P.d) - ω) / ((1 + ω) * (1 - P.beta * ω)) := by
    rw [hP', hM']
    have : (1 - P.beta * ω) ≠ 0 := by linarith
    have : (1 + ω) ≠ 0 := by linarith
    have : (1 - P.d) ≠ 0 := by linarith
    have : P.beta ≠ 0 := hb0.ne'
    have : (1 - ω * P.beta) ≠ 0 := by linarith
    field_simp; ring
  rw [← sub_eq_zero, key]
  constructor
  · intro h
    rcases div_eq_zero_iff.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hb0.ne'
        · exact absurd h (by linarith)
      · linarith
    · exact absurd h hden
  · intro h; rw [h, sub_self, mul_zero, zero_div]
