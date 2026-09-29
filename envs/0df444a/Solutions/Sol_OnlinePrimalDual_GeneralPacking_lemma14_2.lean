-- Prove2me | solution 1 for OnlinePrimalDual.GeneralPacking.lemma14_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:43:54.43755+00:00
-- url     : https://prove2.me/submissions/c5ca13f2-9418-4b7b-8330-1c697876a84c

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_harmonicNum

namespace OnlinePrimalDual.GeneralPacking

theorem aux_l142_swap (y : ℕ → ℝ) : ∀ m : ℕ,
    ∑ j ∈ Finset.Icc 1 m, ((m : ℝ) - j + 1) * y j
      = ∑ j ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 j, y k := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have h1 : ∑ j ∈ Finset.Icc 1 n, (((n + 1 : ℕ) : ℝ) - j + 1) * y j
        = ∑ j ∈ Finset.Icc 1 n, ((n : ℝ) - j + 1) * y j + ∑ j ∈ Finset.Icc 1 n, y j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      push_cast; ring
    rw [h1, ih, Finset.sum_Icc_succ_top (by omega)]
    push_cast; ring

theorem aux_l142_reflect : ∀ m : ℕ,
    ∑ j ∈ Finset.Icc 1 m, 1 / ((m : ℝ) - j + 1) = ∑ i ∈ Finset.Icc 1 m, 1 / (i : ℝ) := by
  intro m
  refine Finset.sum_nbij' (fun j => m + 1 - j) (fun i => m + 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [Nat.cast_sub (by omega)]
    push_cast; ring_nf

end OnlinePrimalDual.GeneralPacking

open OnlinePrimalDual.GeneralPacking

theorem solution (m : ℕ) (hm : 1 ≤ m) (B : ℝ) (hB : 0 < B) (y : ℕ → ℝ)
    (hy_nonneg : ∀ k, 0 ≤ y k)
    (hB_competitive : ∀ j ∈ Finset.Icc 1 m,
      1 / (B * ((m : ℝ) - j + 1)) ≤ ∑ k ∈ Finset.Icc 1 j, y k) :
    harmonicNum m / B ≤ ∑ j ∈ Finset.Icc 1 m, ((m : ℝ) - j + 1) * y j := by
  rw [aux_l142_swap y m]
  have hH : harmonicNum m / B = ∑ j ∈ Finset.Icc 1 m, 1 / (B * ((m : ℝ) - j + 1)) := by
    unfold harmonicNum
    rw [← aux_l142_reflect m, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [div_div, mul_comm]
  rw [hH]
  exact Finset.sum_le_sum hB_competitive
