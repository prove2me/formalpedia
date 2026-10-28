-- Prove2me | solution 1 for SyncPrefix.Huffman.padding
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:03:12.058875+00:00
-- url     : https://prove2.me/submissions/b13d20c7-6081-4431-adcb-0efa2d3656f7

import Definitions.Def_SyncPrefix_Huffman_Complexity
import Theorems.Thm_SyncPrefix_Huffman_sc_disjoint_copies_reduction

open SyncPrefix.Huffman SetCoverThreshold.SetCover

theorem solution (hSC : SetCoverHardness) :
    ∀ γ : ℝ, 0 < γ → ∀ d : ℝ, 0 < d → ∃ c' : ℝ, 0 < c' ∧
      (SCApproxWithinOn
        (fun I => (I.sets.length : ℝ) ≤ (I.n : ℝ) ^ (1 + γ) ∧ d * Real.log I.n ≤ minCover I)
        (fun p => c' * Real.log p) → PEqNP) := by
  intro γ hγ d hd
  obtain ⟨c₀, hc₀, hSC₀⟩ := hSC (2 * γ) (by linarith)
  refine ⟨c₀ / 2, by linarith, fun hApprox => hSC₀ ?_⟩
  rcases hApprox with ⟨Alg, hAlg, n₀, hAlgSpec⟩
  obtain ⟨Alg', hAlg', hRed⟩ := sc_disjoint_copies_reduction Alg hAlg
  refine ⟨Alg', hAlg', max (max n₀ 2) ⌈(4 * d) ^ 2⌉₊, ?_⟩
  intro I hI_sets hCov hnI
  have hn0 : n₀ ≤ I.n := le_trans (le_trans (le_max_left n₀ 2) (le_max_left _ _)) hnI
  have hn2 : 2 ≤ I.n := le_trans (le_trans (le_max_right n₀ 2) (le_max_left _ _)) hnI
  have hnd : ⌈(4 * d) ^ 2⌉₊ ≤ I.n := le_trans (le_max_right _ _) hnI
  obtain ⟨I', hCov', hn', hm', hmin', hmin1, hLen'⟩ := hRed I hCov (by omega)
  have hIn_pos : (0 : ℝ) < I.n := by exact_mod_cast (by omega : 0 < I.n)
  have hm'_le : (I'.sets.length : ℝ) ≤ (I'.n : ℝ) ^ (1 + γ) := by
    have h1 : (I'.sets.length : ℝ) = (I.n : ℝ) * (I.sets.length : ℝ) := by exact_mod_cast hm'
    have h2 : (I.n : ℝ) * (I.sets.length : ℝ) ≤ (I.n : ℝ) * (I.n : ℝ) ^ (1 + 2 * γ) :=
      mul_le_mul_of_nonneg_left hI_sets (by positivity)
    have h3 : (I.n : ℝ) * (I.n : ℝ) ^ (1 + 2 * γ) = (I.n : ℝ) ^ (2 * (1 + γ)) := by
      have hadd := (Real.rpow_add hIn_pos 1 (1 + 2 * γ)).symm
      rw [Real.rpow_one] at hadd
      rw [hadd]
      congr 1
      ring
    have h4 : (I.n : ℝ) ^ (2 * (1 + γ)) = ((I.n : ℝ) ^ (2 : ℝ)) ^ (1 + γ) :=
      Real.rpow_mul (by positivity) 2 (1 + γ)
    have h5 : (I.n : ℝ) ^ (2 : ℝ) = (I'.n : ℝ) := by
      rw [hn']
      have hsq : (I.n : ℝ) ^ (2 : ℝ) = (I.n : ℝ) ^ (2 : ℕ) := Real.rpow_natCast (I.n : ℝ) 2
      rw [hsq]
      push_cast
      rfl
    have h6 : ((I.n : ℝ) ^ (2 : ℝ)) ^ (1 + γ) = (I'.n : ℝ) ^ (1 + γ) := by rw [h5]
    linarith
  have hd_le : d * Real.log I'.n ≤ minCover I' := by
    have hsqrt_pos : 0 < Real.sqrt I.n := Real.sqrt_pos.mpr hIn_pos
    have hlog_sqrt : Real.log (Real.sqrt I.n) ≤ Real.sqrt I.n := by
      linarith [Real.log_le_sub_one_of_pos hsqrt_pos]
    have hlog_In : Real.log (I.n : ℝ) = 2 * Real.log (Real.sqrt I.n) := by
      conv_lhs => rw [← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ I.n)]
      rw [Real.log_pow]
      push_cast
      ring
    have hlog_I'n : Real.log (I'.n : ℝ) = 2 * Real.log (I.n : ℝ) := by
      rw [hn']
      push_cast
      rw [Real.log_pow]
      push_cast
      ring
    have h4d_sq : (4 * d) ^ 2 ≤ (I.n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hnd)
    have h4d : 4 * d ≤ Real.sqrt I.n := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * d)]
      exact Real.sqrt_le_sqrt h4d_sq
    have h_In_bound : d * Real.log (I'.n : ℝ) ≤ I.n := by
      have h_eq : d * Real.log (I'.n : ℝ) = 4 * d * Real.log (Real.sqrt I.n) := by
        rw [hlog_I'n, hlog_In]
        ring
      calc d * Real.log (I'.n : ℝ) = 4 * d * Real.log (Real.sqrt I.n) := h_eq
      _ ≤ 4 * d * Real.sqrt I.n := mul_le_mul_of_nonneg_left hlog_sqrt (by positivity)
      _ ≤ Real.sqrt I.n * Real.sqrt I.n := mul_le_mul_of_nonneg_right h4d (by positivity)
      _ = I.n := Real.mul_self_sqrt (by positivity)
    have h_In_le_min : (I.n : ℝ) ≤ minCover I' := by
      rw [hmin']
      have : I.n * 1 ≤ I.n * minCover I := Nat.mul_le_mul_left I.n hmin1
      exact_mod_cast (by omega : I.n ≤ I.n * minCover I)
    linarith
  have hn0_I' : n₀ ≤ I'.n := by
    rw [hn']
    have : I.n ≤ I.n ^ 2 := by nlinarith
    omega
  have hSpec := hAlgSpec I' ⟨hm'_le, hd_le⟩ hCov' hn0_I'
  dsimp only at hSpec ⊢
  rw [hLen']
  refine ⟨?_, ?_⟩
  · rw [Nat.le_div_iff_mul_le (by omega : 0 < I.n)]
    rw [mul_comm, ← hmin']
    exact hSpec.1
  · have hdiv_mul : (((Alg I'.encode).length / I.n : ℕ) : ℝ) * I.n ≤ (Alg I'.encode).length := by
      exact_mod_cast Nat.div_mul_le_self (Alg I'.encode).length I.n
    have hlog_I'n : Real.log (I'.n : ℝ) = 2 * Real.log (I.n : ℝ) := by
      rw [hn']
      push_cast
      rw [Real.log_pow]
      push_cast
      ring
    have hmin'_real : (minCover I' : ℝ) = (I.n : ℝ) * (minCover I : ℝ) := by exact_mod_cast hmin'
    have hUpper := hSpec.2
    rw [hlog_I'n, hmin'_real] at hUpper
    have h_prod : (((Alg I'.encode).length / I.n : ℕ) : ℝ) * I.n ≤
        (c₀ * Real.log I.n * minCover I) * I.n := by
      linarith
    exact le_of_mul_le_mul_right h_prod hIn_pos
