-- Prove2me | solution 1 for ProxBundle.GPB.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:53:33.662633+00:00
-- url     : https://prove2.me/submissions/9325e7b1-6137-471f-aaf6-785440c3aefd

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Theorems.Thm_ProxBundle_GPB_lemma_4_2

open ProxBundle.GPB

theorem solution {n : ℕ} (P : Instance n) (μ lam ε : ℝ)
    (x0 x0s : E n) (xh yh : ℕ → E n) (Γh : ℕ → E n → ℝ)
    (hμ : 0 ≤ μ) (hA1 : P.A1 μ) (hlam : 0 < lam) (hε : 0 < ε)
    (hhat : IsHat P μ lam ε x0 xh yh Γh)
    (hopt : P.IsNearestOpt x0 x0s) :
    ∃ K : ℕ, 1 ≤ K ∧
      P.φ (yh K) - P.φ x0s ≤ ε ∧
      (∀ i : ℕ, 1 ≤ i → i < K → ε < P.φ (yh i) - P.φ x0s) ∧
      (K : ℝ) ≤ serBound μ lam ε (‖x0 - x0s‖ ^ 2) + 1 ∧
      (∀ k : ℕ, k < K → ‖xh k - x0s‖ ≤ Real.sqrt 2 * ‖x0 - x0s‖) := by
  classical
  have hu : x0s ∈ P.D := hopt.1.1
  obtain ⟨-, hb, hc⟩ := ProxBundle.GPB.lemma_4_2 P μ lam ε x0 x0s xh yh Γh hμ hA1 hlam hε hhat hu
  set S := serBound μ lam ε (‖x0 - x0s‖ ^ 2) with hSdef
  set r := ‖x0 - x0s‖ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hSle : S ≤ r / (lam * ε) := by
    rw [hSdef]; unfold serBound
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hS0 : 0 ≤ S := by
    rw [hSdef]; unfold serBound
    split_ifs with h
    · positivity
    · have hμp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm h)
      have hlm : 0 < lamMu μ lam := by unfold lamMu; positivity
      apply le_min (by positivity)
      apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      have : 0 ≤ μ * r / ε := by positivity
      linarith
  set K0 : ℕ := max 1 ⌈S⌉₊ with hK0
  have hK01 : 1 ≤ K0 := le_max_left _ _
  have hSK0 : S ≤ (K0 : ℝ) := by
    have : S ≤ (⌈S⌉₊ : ℝ) := Nat.le_ceil S
    have h2 : (⌈S⌉₊ : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast le_max_right _ _
    linarith
  have hex : ∃ k : ℕ, 1 ≤ k ∧ P.φ (yh k) - P.φ x0s ≤ ε := by
    obtain ⟨k, hk1, -, hk⟩ := hb K0 hK01 hSK0
    exact ⟨k, hk1, hk⟩
  have hKle : Nat.find hex ≤ K0 := by
    obtain ⟨k, hk1, hkK, hk⟩ := hb K0 hK01 hSK0
    exact (Nat.find_min' hex ⟨hk1, hk⟩).trans hkK
  obtain ⟨hK1, hKsol⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hK1, hKsol, ?_, ?_, ?_⟩
  · intro i hi1 hiK
    have := Nat.find_min hex hiK
    push Not at this
    exact this hi1
  · have hK0S : (K0 : ℝ) ≤ S + 1 := by
      rw [hK0]
      rcases le_total 1 ⌈S⌉₊ with h | h
      · rw [max_eq_right h]
        exact (Nat.ceil_lt_add_one hS0).le
      · rw [max_eq_left h]; push_cast; linarith
    have : (Nat.find hex : ℝ) ≤ K0 := by exact_mod_cast hKle
    linarith
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [hhat.1]
      have : (1:ℝ) ≤ Real.sqrt 2 := by
        rw [Real.one_le_sqrt]; norm_num
      nlinarith [norm_nonneg (x0 - x0s)]
    · -- k < K ≤ K0, so K0 = ⌈S⌉₊ ≥ 2 and k < S
      have hkK0 : k < K0 := lt_of_lt_of_le hk hKle
      have hkS : (k : ℝ) < S := by
        have hceil : k < ⌈S⌉₊ := by
          rw [hK0] at hkK0
          rcases le_total 1 ⌈S⌉₊ with h | h
          · rwa [max_eq_right h] at hkK0
          · rw [max_eq_left h] at hkK0; omega
        exact Nat.lt_ceil.mp hceil
      have hkr : lam * (k : ℝ) * ε ≤ r := by
        have h1 : (k : ℝ) ≤ r / (lam * ε) := by linarith
        rw [le_div_iff₀ (by positivity)] at h1
        linarith
      have hsq := hc hopt.1 k hkpos
      have h2 : ‖xh k - x0s‖ ^ 2 ≤ 2 * ‖x0 - x0s‖ ^ 2 := by rw [← hr]; linarith
      have e : Real.sqrt 2 * ‖x0 - x0s‖ = Real.sqrt (2 * ‖x0 - x0s‖ ^ 2) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
      rw [e]
      exact Real.le_sqrt_of_sq_le h2
