-- Prove2me | solution 1 for SyncPrefix.Huffman.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:03:10.629442+00:00
-- url     : https://prove2.me/submissions/98bf8545-6798-4b84-8072-d4c1766b9998

import Definitions.Def_SyncPrefix_Huffman_Complexity
import Definitions.Def_SyncPrefix_Huffman_Constructions
import Theorems.Thm_SyncPrefix_Huffman_theorem_2_reduction
import Theorems.Thm_SyncPrefix_Huffman_scAutomaton_encode_polyTime
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

open SyncPrefix.Huffman SetCoverThreshold.SetCover

theorem solution (hSC : SetCoverHardness) :
    ∀ γ : ℝ, 0 < γ → ∃ c : ℝ, 0 < c ∧
      (SSWApproxWithin (fun A => StronglyAcyclic A.δ ∧ (A.k : ℝ) ≤ (A.n : ℝ) ^ (1 + γ))
        (fun n => c * Real.log n) → PEqNP) := by
  intro γ hγ
  obtain ⟨c', hc', hSC'⟩ := hSC (2 * γ) (by linarith)
  refine ⟨c' / 3, by linarith, fun hApprox => hSC' ?_⟩
  rcases hApprox with ⟨Alg, hAlg, n₀, hAlgSpec⟩
  rcases scAutomaton_encode_polyTime with ⟨f, hf, hfSpec⟩
  refine ⟨Alg ∘ f, CookPvsNP.polyTimeComputable_comp f Alg hf hAlg, max n₀ 2, ?_⟩
  intro I hI_sets hCov hnI
  have hn0 : n₀ ≤ I.n := le_trans (le_max_left n₀ 2) hnI
  have hn2 : 2 ≤ I.n := le_trans (le_max_right n₀ 2) hnI
  obtain ⟨hnA, hkA, hSA, hSync, hLen⟩ := theorem_2_reduction I hCov
  have hIn_pos : (0 : ℝ) < I.n := by exact_mod_cast (by omega : 0 < I.n)
  have hIn_ge_one : (1 : ℝ) ≤ I.n := by exact_mod_cast (by omega : 1 ≤ I.n)
  have hk_le : ((scAutomaton I).k : ℝ) ≤ ((scAutomaton I).n : ℝ) ^ (1 + γ) := by
    have h1 : ((scAutomaton I).k : ℝ) ≤ (I.n : ℝ) ^ (1 + 2 * γ) := by
      rw [hkA]
      exact hI_sets
    have h2 : (I.n : ℝ) ^ (1 + 2 * γ) ≤ (I.n : ℝ) ^ (2 * (1 + γ)) :=
      Real.rpow_le_rpow_of_exponent_le hIn_ge_one (by linarith)
    have h3 : (I.n : ℝ) ^ (2 * (1 + γ)) = ((I.n : ℝ) ^ (2 : ℝ)) ^ (1 + γ) :=
      Real.rpow_mul (by positivity) 2 (1 + γ)
    have h4 : (I.n : ℝ) ^ (2 : ℝ) ≤ (scAutomaton I).n := by
      rw [hnA]
      have hsq : (I.n : ℝ) ^ (2 : ℝ) = (I.n : ℝ) ^ (2 : ℕ) := Real.rpow_natCast (I.n : ℝ) 2
      rw [hsq]
      push_cast
      linarith
    have h5 : ((I.n : ℝ) ^ (2 : ℝ)) ^ (1 + γ) ≤ ((scAutomaton I).n : ℝ) ^ (1 + γ) :=
      Real.rpow_le_rpow (by positivity) h4 (by linarith)
    linarith
  have hn0_A : n₀ ≤ (scAutomaton I).n := by
    rw [hnA]
    have : I.n ≤ I.n ^ 2 + 1 := by nlinarith
    omega
  have hSpec := hAlgSpec (scAutomaton I) ⟨hSA, hk_le⟩ hSync hn0_A
  simp only [Function.comp_apply, hfSpec I, hLen] at hSpec ⊢
  refine ⟨hSpec.1, le_trans hSpec.2 ?_⟩
  have hlog : Real.log ((scAutomaton I).n : ℝ) ≤ 3 * Real.log (I.n : ℝ) := by
    have hAn_pos : (0 : ℝ) < (scAutomaton I).n := by
      rw [hnA]
      exact_mod_cast (by positivity : 0 < I.n ^ 2 + 1)
    have hAn_cube : (scAutomaton I).n ≤ I.n ^ 3 := by
      rw [hnA]
      nlinarith
    have hlog_cube := Real.log_le_log hAn_pos
      (by exact_mod_cast hAn_cube : ((scAutomaton I).n : ℝ) ≤ ((I.n ^ 3 : ℕ) : ℝ))
    push_cast at hlog_cube
    rw [Real.log_pow] at hlog_cube
    push_cast at hlog_cube
    linarith
  have hc_log : c' / 3 * Real.log ((scAutomaton I).n : ℝ) ≤ c' * Real.log (I.n : ℝ) := by nlinarith
  exact mul_le_mul_of_nonneg_right hc_log (Nat.cast_nonneg _)
