-- Prove2me | solution 1 for SennottDP.Tauberian.cauchy_product_partial_sums
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:59:59.18763+00:00
-- url     : https://prove2.me/submissions/d195b34f-f8de-4368-bb47-9ad16d23299b

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

open scoped ENNReal NNReal Topology in open Filter in open SennottDP.Tauberian in
theorem solution (u : ℕ → ℝ≥0∞) (hfin : ∀ n, u n ≠ ⊤)
    (hR : 1 ≤ radius u) (α : ℝ≥0) (hα : α < 1) :
    (∑' n : ℕ, (α : ℝ≥0∞) ^ n) * U u α = ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) ∧
      ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) = U u α / (1 - (α : ℝ≥0∞)) := by
  have hterm : ∀ n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1)
      = ∑' k : ℕ, (if k ≤ n then (α : ℝ≥0∞) ^ n * u k else 0) := by
    intro n
    unfold w
    rw [Finset.mul_sum, tsum_eq_sum (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    · intro k hk
      rw [if_neg]
      intro hkn
      exact hk (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
  have hinner : ∀ k : ℕ, ∑' n : ℕ, (if k ≤ n then (α : ℝ≥0∞) ^ n * u k else 0)
      = (∑' m : ℕ, (α : ℝ≥0∞) ^ m) * ((α : ℝ≥0∞) ^ k * u k) := by
    intro k
    have hsupp : Function.support (fun n : ℕ => if k ≤ n then (α : ℝ≥0∞) ^ n * u k else 0)
        ⊆ Set.range (fun m : ℕ => m + k) := by
      intro n hn
      by_cases hkn : k ≤ n
      · exact ⟨n - k, Nat.sub_add_cancel hkn⟩
      · rw [Function.mem_support] at hn
        exact (hn (by simp [hkn])).elim
    rw [← ENNReal.tsum_mul_right, ← (add_left_injective k).tsum_eq hsupp]
    refine tsum_congr fun m => ?_
    rw [if_pos (Nat.le_add_left k m), pow_add]
    ring
  have key : (∑' n : ℕ, (α : ℝ≥0∞) ^ n) * U u α
      = ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) := by
    unfold U
    simp_rw [hterm]
    rw [ENNReal.tsum_comm]
    simp_rw [hinner]
    rw [ENNReal.tsum_mul_left]
  refine ⟨key, ?_⟩
  rw [← key, ENNReal.tsum_geometric, div_eq_mul_inv, mul_comm]
