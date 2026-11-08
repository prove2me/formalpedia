-- Prove2me | solution 1 for WinLoseMinimax.example_1_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:11:47.376878+00:00
-- url     : https://prove2.me/submissions/4a939382-bc7c-4069-9014-39968e7aa2cd

import Mathlib
import Definitions.Def_WinLoseMinimax_Game

open scoped ENNReal

namespace Aux_WLMex13

open WinLoseMinimax Filter Topology

theorem pay_right (p : PMF ℕ) (N : ℕ) :
    payoff lng p (PMF.pure N) = ∑' s, p s * (if N ≤ s then 1 else 0) := by
  unfold payoff
  congr 1
  funext s
  rw [tsum_eq_single N]
  · simp [lng]
  · intro t ht
    simp [PMF.pure_apply, ht]

theorem pay_left (q : PMF ℕ) (N : ℕ) :
    payoff lng (PMF.pure N) q = ∑' t, q t * (if t ≤ N then 1 else 0) := by
  unfold payoff
  rw [tsum_eq_single N]
  · congr 1
    funext t
    simp [lng]
  · intro s hs
    simp [PMF.pure_apply, hs]

theorem pay_le_one (p q : PMF ℕ) : payoff lng p q ≤ 1 := by
  unfold payoff
  calc ∑' s, ∑' t, p s * q t * (if lng s t then 1 else 0)
      ≤ ∑' s, ∑' t, p s * q t := by
        apply ENNReal.tsum_le_tsum; intro s
        apply ENNReal.tsum_le_tsum; intro t
        split_ifs <;> simp
    _ = 1 := by
        simp only [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem tail_eq (p : PMF ℕ) (N : ℕ) :
    ∑' s, p s * (if N ≤ s then 1 else 0) = ∑' k, p (k + N) := by
  have h := Summable.sum_add_tsum_nat_add' (f := fun s => p s * (if N ≤ s then 1 else 0)) (k := N)
    ENNReal.summable
  rw [← h]
  have h0 : ∑ i ∈ Finset.range N, p i * (if N ≤ i then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    simp [show ¬ N ≤ i by omega]
  rw [h0, zero_add]
  congr 1
  funext k
  simp

end Aux_WLMex13

open WinLoseMinimax Aux_WLMex13 Filter Topology in
theorem solution :
    (⨆ p : PMF ℕ, ⨅ q : PMF ℕ, payoff lng p q) = 0 ∧
      (⨅ q : PMF ℕ, ⨆ p : PMF ℕ, payoff lng p q) = 1 := by
  constructor
  · apply le_antisymm _ bot_le
    apply iSup_le
    intro p
    have ht := ENNReal.tendsto_sum_nat_add (fun s => p s) (by simp [PMF.tsum_coe])
    apply ge_of_tendsto' ht
    intro N
    rw [← tail_eq, ← pay_right]
    exact iInf_le _ _
  · apply le_antisymm
    · apply (iInf_le _ (PMF.pure 0)).trans
      exact iSup_le (fun p => pay_le_one p _)
    · apply le_iInf
      intro q
      have ht := ENNReal.tendsto_nat_tsum (fun t => q t)
      rw [PMF.tsum_coe] at ht
      apply le_of_tendsto' ht
      intro n
      apply le_trans _ (le_iSup _ (PMF.pure n))
      rw [pay_left]
      calc ∑ t ∈ Finset.range n, q t
          = ∑ t ∈ Finset.range n, q t * (if t ≤ n then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.mem_range] at ht
            simp [show t ≤ n by omega]
        _ ≤ ∑' t, q t * (if t ≤ n then 1 else 0) := ENNReal.sum_le_tsum _
