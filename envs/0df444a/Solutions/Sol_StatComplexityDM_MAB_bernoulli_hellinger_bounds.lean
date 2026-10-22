-- Prove2me | solution 1 for StatComplexityDM.MAB.bernoulli_hellinger_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:46:35.361264+00:00
-- url     : https://prove2.me/submissions/16dc88ac-3205-4300-a526-949f46066365

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_MAB_Bernoulli
set_option autoImplicit false

theorem solution :
    (∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
      FoundationsRL.GeneralDM.hellingerSq (StatComplexityDM.MAB.ber p) (StatComplexityDM.MAB.ber q) ≤ (p - q) ^ 2 * (1 / (p + q) + 1 / (1 - p + (1 - q)))) ∧
    (∀ Δ : ℝ, 0 < Δ → Δ < 1 / 2 →
      FoundationsRL.GeneralDM.hellingerSq (StatComplexityDM.MAB.ber (1 / 2 + Δ)) (StatComplexityDM.MAB.ber (1 / 2)) ≤ 3 * Δ ^ 2) ∧
    (∀ Δ : ℝ, 0 < Δ → Δ < 1 / 4 →
      FoundationsRL.GeneralDM.hellingerSq (StatComplexityDM.MAB.ber (1 / 2 + Δ)) (StatComplexityDM.MAB.ber (1 / 2 + 2 * Δ)) ≤ 5 * Δ ^ 2) := by
  have base : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 * (1 / (a + b)) := by
    intro a b ha hb
    by_cases hab : a + b = 0
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      subst ha0; subst hb0; simp
    · have hpos : 0 < a + b := lt_of_le_of_ne (by linarith) (Ne.symm hab)
      set x := Real.sqrt a with hx
      set y := Real.sqrt b with hy
      have hx0 : 0 ≤ x := Real.sqrt_nonneg a
      have hy0 : 0 ≤ y := Real.sqrt_nonneg b
      have hax : a = x ^ 2 := (Real.sq_sqrt ha).symm
      have hby : b = y ^ 2 := (Real.sq_sqrt hb).symm
      rw [← sub_nonneg]
      have hxy : 0 < x ^ 2 + y ^ 2 := by rw [← hax, ← hby]; exact hpos
      have e : (a - b) ^ 2 * (1 / (a + b)) - (x - y) ^ 2
          = (x - y) ^ 2 * (2 * x * y) / (x ^ 2 + y ^ 2) := by
        rw [hax, hby]
        field_simp
        ring
      rw [e]
      positivity
  have key : ∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
      FoundationsRL.GeneralDM.hellingerSq (StatComplexityDM.MAB.ber p) (StatComplexityDM.MAB.ber q) ≤ (p - q) ^ 2 * (1 / (p + q) + 1 / (1 - p + (1 - q))) := by
    intro p q hp0 hp1 hq0 hq1
    unfold FoundationsRL.GeneralDM.hellingerSq StatComplexityDM.MAB.ber
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    have h1 := base p q hp0 hq0
    have h2 := base (1 - p) (1 - q) (by linarith) (by linarith)
    have e : (p - q) ^ 2 * (1 / (p + q) + 1 / (1 - p + (1 - q)))
        = (p - q) ^ 2 * (1 / (p + q)) + (1 - p - (1 - q)) ^ 2 * (1 / (1 - p + (1 - q))) := by
      ring
    rw [e]
    linarith
  refine ⟨key, ?_, ?_⟩
  · intro Δ hΔ0 hΔ1
    have h := key (1 / 2 + Δ) (1 / 2) (by linarith) (by linarith) (by norm_num) (by norm_num)
    refine h.trans ?_
    have e1 : 1 / (1 / 2 + Δ + 1 / 2) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have e2 : 1 / (1 - (1 / 2 + Δ) + (1 - 1 / 2)) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have e3 : (1 / 2 + Δ - 1 / 2) ^ 2 = Δ ^ 2 := by ring
    rw [e3]
    nlinarith [sq_nonneg Δ]
  · intro Δ hΔ0 hΔ1
    have h := key (1 / 2 + Δ) (1 / 2 + 2 * Δ) (by linarith) (by linarith) (by linarith) (by linarith)
    refine h.trans ?_
    have e1 : 1 / (1 / 2 + Δ + (1 / 2 + 2 * Δ)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have e2 : 1 / (1 - (1 / 2 + Δ) + (1 - (1 / 2 + 2 * Δ))) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have e3 : (1 / 2 + Δ - (1 / 2 + 2 * Δ)) ^ 2 = Δ ^ 2 := by ring
    rw [e3]
    nlinarith [sq_nonneg Δ]
