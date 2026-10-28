-- Prove2me | solution 1 for SyncPrefix.Huffman.corollary_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:08:54.45683+00:00
-- url     : https://prove2.me/submissions/8230ff38-2d01-4364-8a50-c717086a84d4

import Definitions.Def_SyncPrefix_Huffman_Complexity
import Definitions.Def_SyncPrefix_Huffman_Constructions
import Theorems.Thm_SyncPrefix_Huffman_padding
import Theorems.Thm_SyncPrefix_Huffman_theorem_2_reduction
import Theorems.Thm_SyncPrefix_Huffman_scAutomaton_encode_polyTime
import Theorems.Thm_SyncPrefix_Huffman_lemma_5
import Theorems.Thm_SyncPrefix_Huffman_wielandt_code
import Theorems.Thm_SyncPrefix_Huffman_composition_decoder
import Theorems.Thm_SyncPrefix_Huffman_composition_bounds
import Theorems.Thm_SyncPrefix_Huffman_wielandt_encoding_reduction
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

open SyncPrefix.Huffman SetCoverThreshold.SetCover

theorem solution (hSC : SetCoverHardness) :
    ∃ c : ℝ, 0 < c ∧
      (SSWApproxWithin (fun A => A.k = 2 ∧ IsHuffmanDecoder A.δ) (fun n => c * Real.log n) →
        PEqNP) := by
  obtain ⟨c', hc', hPad⟩ := padding hSC 1 zero_lt_one 8 (by norm_num)
  refine ⟨c' / 15, by linarith, fun hApprox => hPad ?_⟩
  rcases hApprox with ⟨Alg, hAlg, n₀, hAlgSpec⟩
  obtain ⟨f_sc, hf_sc, hf_sc_spec⟩ := scAutomaton_encode_polyTime
  obtain ⟨f₅, hf₅, hf₅_spec⟩ := lemma_5
  obtain ⟨Alg_H, hAlg_H, hWielandt⟩ := wielandt_encoding_reduction Alg hAlg
  have hComp1 := CookPvsNP.polyTimeComputable_comp f_sc f₅ hf_sc hf₅
  have hComp2 := CookPvsNP.polyTimeComputable_comp (f₅ ∘ f_sc) Alg_H hComp1 hAlg_H
  refine ⟨Alg_H ∘ (f₅ ∘ f_sc), hComp2, max (max n₀ 36) ⌈Real.exp 1⌉₊, ?_⟩
  intro I ⟨hI_sets, hI_min⟩ hCov hnI
  have hn0 : n₀ ≤ I.n := le_trans (le_trans (le_max_left n₀ 36) (le_max_left _ _)) hnI
  have hn36 : 36 ≤ I.n := le_trans (le_trans (le_max_right n₀ 36) (le_max_left _ _)) hnI
  have hn_exp : ⌈Real.exp 1⌉₊ ≤ I.n := le_trans (le_max_right _ _) hnI
  obtain ⟨hnA, hkA, hSA, hSyncA, hLenA⟩ := theorem_2_reduction I hCov
  obtain ⟨AH, hf₅A, hHuffAH, hkAH, hSyncAH, hLenAH, hnAH_ge, hnAH_le⟩ :=
    hf₅_spec (scAutomaton I) hSA hSyncA
  have hnAH_ge2 : 2 ≤ AH.n := by nlinarith
  have hkAH_ge2 : 2 ≤ AH.k := by omega
  obtain ⟨L, δY, e, AB, hL1, hL_le, hHuffY, hSyncY, hLenY, hkAB, hnAB_ge, hnAB_le,
    hHuffAB_imp, hSyncAB_imp, hLenAB, hAlgH_len⟩ :=
    hWielandt AH hHuffAH hSyncAH hnAH_ge2 hkAH_ge2
  obtain ⟨hMaxZ, -, hmZ, hMZ, ⟨wZ, hwZ_len, hwZ⟩, -⟩ := wielandt_code L hL1
  have hHuffAB : IsHuffmanDecoder AB.δ :=
    hHuffAB_imp ((composition_decoder δY (wielandtCode L) hMaxZ e).2.2.1 hHuffY)
  obtain ⟨hSyncComp, hCompLower, hCompUpper⟩ :=
    composition_bounds δY (wielandtCode L) hMaxZ e L (L + 1) hmZ hMZ wZ hwZ hSyncY
  have hSyncAB : IsSynchronizing AB.δ := hSyncAB_imp hSyncComp
  clear hHuffAB_imp hSyncAB_imp hSyncComp hMaxZ hmZ hMZ hwZ
  have hAB_lower : L * minCover I ≤ syncLength AB.δ := by
    rw [← hLenAB, hLenY, hLenAH, hLenA] at hCompLower
    exact hCompLower
  have hAB_upper_wZ : syncLength AB.δ ≤ (L + 1) * minCover I + L ^ 2 := by
    rw [← hLenAB, hLenY, hLenAH, hLenA] at hCompUpper
    omega
  clear hCompLower hCompUpper hwZ_len hLenAB hLenY hHuffY hSyncY δY e wZ
  have hIn_ge36 : (36 : ℝ) ≤ I.n := by exact_mod_cast hn36
  have hIn_pos : (0 : ℝ) < I.n := by linarith
  have hlog_In_ge1 : (1 : ℝ) ≤ Real.log I.n := by
    have hexp_le : Real.exp 1 ≤ I.n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn_exp)
    have hlog := Real.log_le_log (Real.exp_pos 1) hexp_le
    rwa [Real.log_exp] at hlog
  have hI_sets_sq : (I.sets.length : ℝ) ≤ (I.n : ℝ) ^ (2 : ℕ) := by
    have h2 : (I.n : ℝ) ^ (1 + (1 : ℝ)) = (I.n : ℝ) ^ (2 : ℕ) := by
      rw [show (1 + 1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    linarith
  have hkAH_real : (AH.k : ℝ) ≤ 2 * (I.n : ℝ) ^ (2 : ℕ) := by
    have h1 : (AH.k : ℝ) = (I.sets.length : ℝ) + 2 := by
      rw [hkAH, hkA]
      push_cast
      rfl
    nlinarith
  have hkAH_cube : (AH.k : ℝ) ≤ (I.n : ℝ) ^ (3 : ℕ) := by
    calc (AH.k : ℝ) ≤ 2 * (I.n : ℝ) ^ (2 : ℕ) := hkAH_real
    _ ≤ (I.n : ℝ) * (I.n : ℝ) ^ (2 : ℕ) := by nlinarith
    _ = (I.n : ℝ) ^ (3 : ℕ) := by ring
  have hlog_AHk : Real.log (AH.k : ℝ) ≤ 3 * Real.log (I.n : ℝ) := by
    have hAHk_pos : (0 : ℝ) < AH.k := by exact_mod_cast (by omega : 0 < AH.k)
    have hlog := Real.log_le_log hAHk_pos hkAH_cube
    rw [Real.log_pow] at hlog
    push_cast at hlog
    linarith
  have hL_le_min : L ≤ minCover I := by
    have hL_real : (L : ℝ) ≤ (minCover I : ℝ) := by linarith
    exact Nat.cast_le.mp hL_real
  have hAB_upper : syncLength AB.δ ≤ 3 * L * minCover I := by
    nlinarith
  have hn0_AB : n₀ ≤ AB.n := by
    have : I.n ≤ I.n ^ 2 + 1 := by nlinarith
    omega
  have hSpec := hAlgSpec AB ⟨hkAB, hHuffAB⟩ hSyncAB hn0_AB
  dsimp only [Function.comp_apply] at hSpec ⊢
  rw [hf_sc_spec I, hf₅A, hAlgH_len]
  refine ⟨?_, ?_⟩
  · rw [Nat.le_div_iff_mul_le (by omega : 0 < L)]
    rw [mul_comm]
    exact le_trans hAB_lower hSpec.1
  · have hAHn_real : (AH.n : ℝ) ≤ 3 * (I.n : ℝ) ^ (2 : ℕ) := by
      have h1 : AH.n ≤ 2 * (I.n ^ 2 + 1) := by omega
      have h2 : (AH.n : ℝ) ≤ 2 * ((I.n : ℝ) ^ (2 : ℕ) + 1) := by exact_mod_cast h1
      nlinarith
    have hABn_real : (AB.n : ℝ) ≤ 6 * (AH.n : ℝ) * (AH.k : ℝ) := by
      exact_mod_cast hnAB_le
    have hABn_pow5 : (AB.n : ℝ) ≤ (I.n : ℝ) ^ (5 : ℕ) := by
      have hmul : 6 * (AH.n : ℝ) * (AH.k : ℝ) ≤
          6 * (3 * (I.n : ℝ) ^ (2 : ℕ)) * (2 * (I.n : ℝ) ^ (2 : ℕ)) := by
        have h_nonneg : 0 ≤ (AH.k : ℝ) := by positivity
        nlinarith
      calc (AB.n : ℝ) ≤ 6 * (AH.n : ℝ) * (AH.k : ℝ) := hABn_real
      _ ≤ 6 * (3 * (I.n : ℝ) ^ (2 : ℕ)) * (2 * (I.n : ℝ) ^ (2 : ℕ)) := hmul
      _ = 36 * ((I.n : ℝ) ^ (2 : ℕ)) ^ 2 := by ring
      _ ≤ (I.n : ℝ) * ((I.n : ℝ) ^ (2 : ℕ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hIn_ge36 (by positivity)
      _ = (I.n : ℝ) ^ (5 : ℕ) := by ring
    have hlog_ABn : Real.log (AB.n : ℝ) ≤ 5 * Real.log (I.n : ℝ) := by
      have hABn_pos : (0 : ℝ) < AB.n := by exact_mod_cast (by omega : 0 < AB.n)
      have hlog := Real.log_le_log hABn_pos hABn_pow5
      rw [Real.log_pow] at hlog
      push_cast at hlog
      linarith
    have hL_pos_real : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    have hdiv_mul : (((Alg AB.encode).length / L : ℕ) : ℝ) * L ≤ (Alg AB.encode).length := by
      exact_mod_cast Nat.div_mul_le_self (Alg AB.encode).length L
    have hAB_upper_real : (syncLength AB.δ : ℝ) ≤ 3 * (L : ℝ) * (minCover I : ℝ) := by
      exact_mod_cast hAB_upper
    have hlog_In_nonneg : 0 ≤ Real.log (I.n : ℝ) := by linarith
    have hStep1a : c' / 15 * Real.log (AB.n : ℝ) ≤ c' / 15 * (5 * Real.log (I.n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ABn (by positivity)
    have hStep1b : c' / 15 * Real.log (AB.n : ℝ) * (syncLength AB.δ : ℝ) ≤
        c' / 15 * (5 * Real.log (I.n : ℝ)) * (syncLength AB.δ : ℝ) :=
      mul_le_mul_of_nonneg_right hStep1a (by positivity)
    have hStep1c : c' / 15 * (5 * Real.log (I.n : ℝ)) * (syncLength AB.δ : ℝ) ≤
        c' / 15 * (5 * Real.log (I.n : ℝ)) * (3 * (L : ℝ) * (minCover I : ℝ)) :=
      mul_le_mul_of_nonneg_left hAB_upper_real (by positivity)
    have hStep1 : ((Alg AB.encode).length : ℝ) ≤
        (c' / 15 * (5 * Real.log (I.n : ℝ))) * (3 * (L : ℝ) * (minCover I : ℝ)) :=
      le_trans hSpec.2 (le_trans hStep1b hStep1c)
    have hEq : (c' / 15 * (5 * Real.log (I.n : ℝ))) * (3 * (L : ℝ) * (minCover I : ℝ)) =
        (c' * Real.log (I.n : ℝ) * (minCover I : ℝ)) * L := by ring
    have hStep2 : (((Alg AB.encode).length / L : ℕ) : ℝ) * L ≤
        (c' * Real.log (I.n : ℝ) * (minCover I : ℝ)) * L :=
      le_trans hdiv_mul (hEq ▸ hStep1)
    exact le_of_mul_le_mul_right hStep2 hL_pos_real
