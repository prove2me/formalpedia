-- Prove2me | solution 1 for QAlgorithms.DeWolf.ldc_two_query_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:49:52.721022+00:00
-- url     : https://prove2.me/submissions/f5d8cee7-8694-4f96-8473-0c20afa8b8b7

import Definitions.Def_QAlgorithms_Defs_Information
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic
import Theorems.Thm_QAlgorithms_DeWolf_ldc_decoder_normalForm
import Theorems.Thm_QAlgorithms_DeWolf_nayak_qrac_lower_bound
import Theorems.Thm_QAlgorithms_DeWolf_parityMatchings_qrac
import Theorems.Thm_QAlgorithms_DeWolf_binEntropy2_gap_quadratic

open QAlgorithms
open scoped ENNReal

private lemma bool_probs (p : PMF Bool) : (p false).toReal + (p true).toReal = 1 := by
  have h : p false + p true = 1 := by
    simpa [tsum_fintype, Fintype.sum_bool, add_comm] using p.tsum_coe
  rw [← ENNReal.toReal_add (p.apply_ne_top false) (p.apply_ne_top true), h]
  simp

private lemma ldc_injective {n N q : ℕ} {δ ε : ℝ}
    {C : (Fin n → Bool) → (Fin N → Bool)} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hC : IsLDC q δ ε C) : Function.Injective C := by
  intro x y hxy
  funext i
  obtain ⟨R, _, hR⟩ := hC i
  have hx := hR x (C x) (by simp; positivity)
  have hy := hR y (C x) (by rw [hxy]; simp; positivity)
  by_contra h
  have hs := bool_probs (R.map fun t => t.eval (C x))
  unfold successProb at hx hy
  cases hxi : x i <;> cases hyi : y i <;> simp_all <;> linarith

private lemma ldc_length {n N q : ℕ} {δ ε : ℝ}
    {C : (Fin n → Bool) → (Fin N → Bool)} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hC : IsLDC q δ ε C) : n ≤ N := by
  have hc := Fintype.card_le_of_injective C (ldc_injective hδ hε hC)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (n N : ℕ) (δ ε : ℝ) (C : (Fin n → Bool) → (Fin N → Bool)),
        n₀ ≤ n → 0 < δ → 0 < ε → IsLDC 2 δ ε C →
        (2 : ℝ) ^ (c * δ ^ 2 * ε ^ 4 * (n : ℝ)) ≤ (N : ℝ) := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hnormal⟩ := QAlgorithms.DeWolf.ldc_decoder_normalForm
  let A : ℝ := c₁ * c₂ / 16
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A ^ 2 / 3, by positivity, 2, ?_⟩
  intro n N δ ε C hn hδ hε hC
  have hnN := ldc_length hδ.le hε hC
  have hN : 2 ≤ N := hn.trans hnN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let η : ℝ := c₁ * (δ * ε / 4)
  let κ : ℝ := c₂ * (ε / 4)
  have hη : 0 < η := by dsimp [η]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hfamilies : ∀ i : Fin n, ∃ M : Finset (Finset (Fin N)),
      (M : Set (Finset (Fin N))).PairwiseDisjoint id ∧
      (∀ t ∈ M, t.card ≤ 2) ∧ η * (N : ℝ) ≤ (M.card : ℝ) ∧
      ∃ a : Finset (Fin N) → Bool, ∀ t ∈ M,
        1 / 2 + κ ≤
          ((Finset.univ.filter fun x : Fin n → Bool =>
            x i = xor (a t) (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) /
              (2 : ℝ) ^ n := by
    intro i
    obtain ⟨M, hdis, hsize, hcard, a, ha⟩ := hnormal n N 2 δ ε C hδ hε hC i
    refine ⟨M, hdis, hsize, ?_, a, ?_⟩
    · convert hcard using 1 <;> dsimp [η] <;> ring
    · intro t ht
      convert ha t ht using 1 <;> norm_num [κ]
  obtain ⟨hbudget, m, ρ, hm, hρ⟩ := QAlgorithms.DeWolf.parityMatchings_qrac
    (by omega) (by omega) C η κ hη hκ hfamilies
  have hb : 0 < η * κ := mul_pos hη hκ
  have hdim := QAlgorithms.DeWolf.nayak_qrac_lower_bound ρ (1 / 2 + η * κ)
    (by linarith) (by linarith) hρ
  have he := QAlgorithms.DeWolf.binEntropy2_gap_quadratic (η * κ) hb.le hbudget
  have hbound : (η * κ) ^ 2 * (n : ℝ) ≤ Real.logb 2 (N : ℝ) + 2 :=
    ((mul_le_mul_of_nonneg_right he (Nat.cast_nonneg n)).trans hdim).trans hm
  have hlog : (1 : ℝ) ≤ Real.logb 2 (N : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hNr]
    simpa using (show (2 : ℝ) ≤ N by exact_mod_cast hN)
  have hprod : η * κ = A * δ * ε ^ 2 := by dsimp [η, κ, A]; ring
  rw [hprod] at hbound
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hNr).1
  nlinarith [hbound]
