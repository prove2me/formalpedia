-- Prove2me | solution 1 for WrightPDIPM.Potential.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:37:53.296349+00:00
-- url     : https://prove2.me/submissions/9863e420-d86e-4996-ac8b-2eb84a92ae38

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting
open Matrix
open WrightPDIPM.Potential

theorem g69b_log_quad (t a τ : ℝ) (ha : |t| ≤ τ) (hτ : τ < 1) :
    -Real.log (1 + t) ≤ -t + t ^ 2 / (2 * (1 - τ)) := by
  have hta : |t| < 1 := lt_of_le_of_lt ha hτ
  have h1 : |(-t)| < 1 := by rwa [abs_neg]
  have hS := Real.hasSum_pow_div_log_of_abs_lt_one h1
  rw [sub_neg_eq_add] at hS
  have hS' := (hasSum_nat_add_iff' (f := fun n : ℕ => (-t) ^ (n + 1) / (n + 1)) 1).mpr hS
  simp only [Finset.range_one, Finset.sum_singleton] at hS'
  set b := |t|
  have hb0 : 0 ≤ b := abs_nonneg t
  have hG : HasSum (fun n : ℕ => b ^ 2 / 2 * b ^ n) (b ^ 2 / 2 * (1 - b)⁻¹) :=
    (hasSum_geometric_of_lt_one hb0 hta).mul_left _
  have hle := hasSum_le (fun n => ?_) hS' hG
  · have hb2 : b ^ 2 = t ^ 2 := sq_abs t
    have h1b : 0 < 1 - b := by linarith
    have h1τ : 0 < 1 - τ := by linarith
    have : b ^ 2 / 2 * (1 - b)⁻¹ ≤ t ^ 2 / (2 * (1 - τ)) := by
      rw [hb2, ← div_eq_mul_inv, div_div]
      apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
      linarith
    norm_num at hle
    linarith
  · show _ ≤ _
    have e : b ^ 2 / 2 * b ^ n = b ^ (n + 1 + 1) / 2 := by ring
    rw [e]
    have hpow : (-t) ^ (n + 1 + 1) ≤ b ^ (n + 1 + 1) := by
      calc (-t) ^ (n + 1 + 1) ≤ |(-t) ^ (n + 1 + 1)| := le_abs_self _
        _ = b ^ (n + 1 + 1) := by rw [abs_pow, abs_neg]
    have hc : ((n + 1 : ℕ) : ℝ) + 1 ≥ 2 := by push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    calc (-t) ^ (n + 1 + 1) / (((n + 1 : ℕ) : ℝ) + 1) ≤ b ^ (n + 1 + 1) / (((n + 1 : ℕ) : ℝ) + 1) :=
          div_le_div_of_nonneg_right hpow (by linarith)
      _ ≤ b ^ (n + 1 + 1) / 2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hc

theorem g69b_lemma_4_1_ii (n : ℕ) (t : Fin n → ℝ) (τ : ℝ) (h1 : normInf t ≤ τ) (h2 : τ < 1) :
    -∑ i, Real.log (1 + t i) ≤ -∑ i, t i + norm2 t ^ 2 / (2 * (1 - τ)) := by
  have hle : ∀ i, |t i| ≤ τ := fun i =>
    le_trans (le_ciSup (Finite.bddAbove_range (fun j => |t j|)) i) h1
  unfold norm2
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), Finset.sum_div,
    ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => g69b_log_quad (t i) 0 τ (hle i) h2)

theorem solution :
    (∀ β : ℝ, -1 < β → Real.log (1 + β) ≤ β ∧ (Real.log (1 + β) = β ↔ β = 0)) ∧
    (∀ (n : ℕ) (t : Fin n → ℝ) (τ : ℝ), normInf t ≤ τ → τ < 1 →
      -∑ i, Real.log (1 + t i) ≤ -∑ i, t i + norm2 t ^ 2 / (2 * (1 - τ))) := by
  refine ⟨fun β hβ => ?_, g69b_lemma_4_1_ii⟩
  have hp : 0 < 1 + β := by linarith
  have h := Real.log_le_sub_one_of_pos hp
  refine ⟨by linarith, ⟨fun he => ?_, fun he => by subst he; simp⟩⟩
  by_contra hne
  have := Real.log_lt_sub_one_of_pos hp (by intro h'; apply hne; linarith)
  linarith
