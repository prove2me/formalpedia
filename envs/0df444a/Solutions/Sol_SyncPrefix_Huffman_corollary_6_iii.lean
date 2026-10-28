-- Prove2me | solution 1 for SyncPrefix.Huffman.corollary_6_iii
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:17:34.32602+00:00
-- url     : https://prove2.me/submissions/ff6582cf-ad94-4a15-b526-77b59b9f88c1

import Definitions.Def_SyncPrefix_Huffman_Complexity
import Theorems.Thm_SyncPrefix_Huffman_theorem_2
import Theorems.Thm_SyncPrefix_Huffman_lemma_5
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

open SyncPrefix.Huffman

theorem solution (hSC : SetCoverHardness) :
    ∀ γ : ℝ, 0 < γ → ∃ c : ℝ, 0 < c ∧
      (SSWApproxWithin (fun A => IsHuffmanDecoder A.δ ∧ (A.k : ℝ) ≤ (A.n : ℝ) ^ (1 + γ))
        (fun n => c * Real.log n) → PEqNP) := by
  intro γ hγ
  obtain ⟨c', hc', hThm2⟩ := theorem_2 hSC (γ / 2) (by linarith)
  refine ⟨c' / 2, by linarith, fun hApprox => hThm2 ?_⟩
  rcases hApprox with ⟨Alg, hAlg, n₀, hAlgSpec⟩
  rcases lemma_5 with ⟨f, hf, hfSpec⟩
  refine ⟨Alg ∘ f, CookPvsNP.polyTimeComputable_comp f Alg hf hAlg,
    max (max n₀ 2) ⌈(3 : ℝ) ^ (2 / γ)⌉₊, ?_⟩
  intro A ⟨hSA, hkA⟩ hSync hnA
  have hn0 : n₀ ≤ A.n := le_trans (le_trans (le_max_left n₀ 2) (le_max_left _ _)) hnA
  have hn2 : 2 ≤ A.n := le_trans (le_trans (le_max_right n₀ 2) (le_max_left _ _)) hnA
  have hn3 : ⌈(3 : ℝ) ^ (2 / γ)⌉₊ ≤ A.n := le_trans (le_max_right _ _) hnA
  obtain ⟨AH, hfA, hHuff, hkAH, hSyncH, hLen, hn_le, hn_le2⟩ := hfSpec A hSA hSync
  have hnA_pos : (0 : ℝ) < A.n := by exact_mod_cast (by omega : 0 < A.n)
  have hnA_ge_one : (1 : ℝ) ≤ A.n := by exact_mod_cast (by omega : 1 ≤ A.n)
  have h3_le : (3 : ℝ) ≤ (A.n : ℝ) ^ (γ / 2) := by
    have hceil : (3 : ℝ) ^ (2 / γ) ≤ A.n :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hn3)
    have hpow := Real.rpow_le_rpow (by positivity) hceil (by linarith : (0 : ℝ) ≤ γ / 2)
    rw [← Real.rpow_mul (by positivity)] at hpow
    have hmul : 2 / γ * (γ / 2) = 1 := by field_simp
    rw [hmul, Real.rpow_one] at hpow
    exact hpow
  have hkAH_le : (AH.k : ℝ) ≤ (AH.n : ℝ) ^ (1 + γ) := by
    have h1_le : (1 : ℝ) ≤ (A.n : ℝ) ^ (1 + γ / 2) :=
      Real.one_le_rpow hnA_ge_one (by linarith)
    have h_split : (A.n : ℝ) ^ (1 + γ) = (A.n : ℝ) ^ (1 + γ / 2) * (A.n : ℝ) ^ (γ / 2) := by
      rw [← Real.rpow_add hnA_pos]
      congr 1
      ring
    have h_step1 : (AH.k : ℝ) ≤ (A.n : ℝ) ^ (1 + γ / 2) + 2 := by
      rw [hkAH]
      push_cast
      linarith
    have h_step2 : (A.n : ℝ) ^ (1 + γ / 2) + 2 ≤ (A.n : ℝ) ^ (1 + γ) := by
      rw [h_split]
      nlinarith
    have h_step3 : (A.n : ℝ) ^ (1 + γ) ≤ (AH.n : ℝ) ^ (1 + γ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_le) (by linarith)
    linarith
  have hSpec := hAlgSpec AH ⟨hHuff, hkAH_le⟩ hSyncH (le_trans hn0 hn_le)
  simp only [Function.comp_apply, hfA, hLen] at hSpec ⊢
  refine ⟨hSpec.1, le_trans hSpec.2 ?_⟩
  have hlog : Real.log (AH.n : ℝ) ≤ 2 * Real.log (A.n : ℝ) := by
    have hAH_pos : (0 : ℝ) < AH.n := by exact_mod_cast (by omega : 0 < AH.n)
    have hAH_sq : AH.n ≤ A.n ^ 2 := by
      calc AH.n ≤ 2 * A.n := hn_le2
      _ ≤ A.n * A.n := Nat.mul_le_mul_right A.n hn2
      _ = A.n ^ 2 := (sq A.n).symm
    have hlog_sq := Real.log_le_log hAH_pos (by exact_mod_cast hAH_sq : (AH.n : ℝ) ≤ ((A.n ^ 2 : ℕ) : ℝ))
    push_cast at hlog_sq
    rw [Real.log_pow] at hlog_sq
    push_cast at hlog_sq
    linarith
  have hc_log : c' / 2 * Real.log (AH.n : ℝ) ≤ c' * Real.log (A.n : ℝ) := by nlinarith
  exact mul_le_mul_of_nonneg_right hc_log (Nat.cast_nonneg _)
