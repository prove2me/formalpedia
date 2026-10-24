-- Prove2me | solution 1 for PosetSecretary.ProxyLabel.selection_prob_top_k
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:19:46.66698+00:00
-- url     : https://prove2.me/submissions/fedfd80a-db4c-42c7-8857-c580b5867680

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting
import Theorems.Thm_PosetSecretary_ProxyLabel_label_max_prob
import Theorems.Thm_PosetSecretary_ProxyLabel_selection_prob_given_label_max
import Theorems.Thm_PosetSecretary_ProxyLabel_exp_neg_c_step

open PosetSecretary.ProxyLabel

theorem solution {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : IsConsistentScoring w) (k : ℕ) (hk : 1 ≤ k) (ω' : ℕ) (c : ℝ)
    (hc : 1 ≤ c) (hω' : (AppliedComb.Posets.width α : ℝ) / c ≤ ω') (a : α)
    (htop : (Finset.univ.filter (fun b => w a < w b)).card < k) :
    (1 - 1 / (k : ℝ)) ^ (k - 1) * (1 / (Real.exp c * (ω' + 1))) ≤ selectionProb k ω' a := by
  classical
  set N := Fintype.card α
  set A0 : ℝ := (1 / (ω' + 1 : ℝ)) * (1 - 1 / (ω' + 1 : ℝ)) ^ AppliedComb.Posets.width α
  set r := (Finset.univ.filter (fun b => w a < w b)).card
  obtain ⟨hL, hL2, -⟩ := label_max_prob w hw.2.1 k hk a (r + 1) (by omega) (by omega)
    (by simp [r])
  have hstep := exp_neg_c_step (AppliedComb.Posets.width α) ω' c hc hω'
  have hp0 : 0 ≤ sampleProb ω' := by unfold sampleProb; positivity
  have hp1 : sampleProb ω' ≤ 1 := by
    unfold sampleProb; rw [div_le_one (by positivity)]; linarith
  have hB : ∀ m, 0 ≤ binomWeight N m (sampleProb ω') := by
    intro m; unfold binomWeight
    have : 0 ≤ 1 - sampleProb ω' := by linarith
    positivity
  set g : (α → Fin k) → ℝ := fun ℓ => ∑ pos : α ≃ Fin N, ∑ m ∈ Finset.range (N + 1),
        (1 / (N.factorial : ℝ)) * binomWeight N m (sampleProb ω') *
          (if a ∈ selected pos ℓ m then 1 else 0) with hg
  have hg0 : ∀ ℓ, 0 ≤ g ℓ := by
    intro ℓ
    refine Finset.sum_nonneg fun pos _ => Finset.sum_nonneg fun m _ => ?_
    have := hB m
    split_ifs <;> positivity
  set G := Finset.univ.filter (fun ℓ : α → Fin k => ∀ b, w a < w b → ℓ b ≠ ℓ a)
  have hgG : ∀ ℓ ∈ G, A0 ≤ g ℓ := by
    intro ℓ hℓ
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    exact selection_prob_given_label_max w hw k hk ω' a ℓ hℓ
  have hsel : selectionProb k ω' a = ∑ ℓ : α → Fin k, (1 / (k : ℝ) ^ N) * g ℓ := by
    unfold selectionProb
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun pos _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have hkpos : 0 < (1 / (k : ℝ) ^ N) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hmain : labelMaxProb w k a * A0 ≤ selectionProb k ω' a := by
    rw [hsel]
    calc labelMaxProb w k a * A0 = ∑ ℓ ∈ G, (1 / (k : ℝ) ^ N) * A0 := by
          rw [Finset.sum_const, nsmul_eq_mul]; unfold labelMaxProb; simp only [G]; ring
      _ ≤ ∑ ℓ ∈ G, (1 / (k : ℝ) ^ N) * g ℓ :=
          Finset.sum_le_sum fun ℓ hℓ => mul_le_mul_of_nonneg_left (hgG ℓ hℓ) hkpos.le
      _ ≤ ∑ ℓ : α → Fin k, (1 / (k : ℝ) ^ N) * g ℓ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun ℓ _ _ => mul_nonneg hkpos.le (hg0 ℓ))
  have hq0 : 0 ≤ (1 - 1 / (k : ℝ)) ^ (k - 1) := by
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : k = 1 := by omega
      subst this; simp
    · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast h2
      have : 0 ≤ 1 - 1 / (k : ℝ) := by
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      positivity
  have hA0 : 0 ≤ 1 / (Real.exp c * (ω' + 1)) := by positivity
  rw [hL] at hmain
  calc (1 - 1 / (k : ℝ)) ^ (k - 1) * (1 / (Real.exp c * (ω' + 1)))
      ≤ (1 - 1 / (k : ℝ)) ^ (r + 1 - 1) * A0 := mul_le_mul hL2 hstep hA0 (le_trans hq0 hL2)
    _ ≤ selectionProb k ω' a := hmain
