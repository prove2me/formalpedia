-- Prove2me | solution 1 for StrictCompatLB.RegularDegree.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T11:54:50.005731+00:00
-- url     : https://prove2.me/submissions/cb55e161-7a43-4876-8c28-668e3acc7405

import Mathlib

open Finset Filter Topology

theorem solution (p : ℕ → ℝ) (hp0 : ∀ N, 0 ≤ p N) (hp1 : ∀ N, p N ≤ 1)
    (hp : Tendsto p atTop (𝓝 0)) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ a : ℝ, 0 < a ∧ ∀ N ≥ N₀,
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k : ℕ => δ * (N : ℝ) ≤ (k : ℝ)),
          (N.choose k : ℝ) * p N ^ k * (1 - p N) ^ (N - k)
        ≤ (a * p N ^ δ) ^ N := by
  refine ⟨1, le_rfl, 2, by norm_num, fun N hN => ?_⟩
  have h0 := hp0 N
  have h1 := hp1 N
  have hrhs : (2 * p N ^ δ) ^ N = (2:ℝ) ^ N * p N ^ (δ * N) := by
    rw [mul_pow, Real.rpow_mul h0, Real.rpow_natCast]
  rw [hrhs]
  calc ∑ k ∈ (Finset.range (N + 1)).filter (fun k : ℕ => δ * (N : ℝ) ≤ (k : ℝ)),
          (N.choose k : ℝ) * p N ^ k * (1 - p N) ^ (N - k)
      ≤ ∑ k ∈ (Finset.range (N + 1)).filter (fun k : ℕ => δ * (N : ℝ) ≤ (k : ℝ)),
          (N.choose k : ℝ) * p N ^ (δ * N) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_filter] at hk
        have hpk : p N ^ k ≤ p N ^ (δ * N) := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_ge' h0 h1 (by positivity) hk.2
        have hq : (1 - p N) ^ (N - k) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
        have hc : (0:ℝ) ≤ N.choose k := by positivity
        have hpk0 : 0 ≤ p N ^ k := pow_nonneg h0 k
        have hq0 : 0 ≤ (1 - p N) ^ (N - k) := pow_nonneg (by linarith) _
        calc (N.choose k : ℝ) * p N ^ k * (1 - p N) ^ (N - k)
            ≤ (N.choose k : ℝ) * p N ^ k * 1 := by gcongr
          _ ≤ (N.choose k : ℝ) * p N ^ (δ * N) := by rw [mul_one]; gcongr
    _ ≤ ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * p N ^ (δ * N) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro k _ _; have := Real.rpow_nonneg h0 (δ * N); positivity
    _ = (2:ℝ) ^ N * p N ^ (δ * N) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose N
