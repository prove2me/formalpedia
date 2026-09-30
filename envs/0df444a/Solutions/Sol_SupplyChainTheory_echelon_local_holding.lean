-- Prove2me | solution 1 for SupplyChainTheory.echelon_local_holding
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:07:53.434752+00:00
-- url     : https://prove2.me/submissions/ce4c0ef6-aea5-4db5-a3c9-48748b22c7e9

import Mathlib
import Definitions.Def_SupplyChainTheory_multiechelon

set_option autoImplicit false

/-- Abel-summation closed form: `∑ (h'ⱼ - h'ⱼ₊₁) Aⱼ + h'_{N+1} A_N = ∑ h'ⱼ aⱼ`,
where `Aⱼ = ∑_{i=1}^j aᵢ`. -/
lemma sct_abel_9138e353 (h' a : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (h' j - h' (j + 1)) * (∑ i ∈ Finset.Icc 1 j, a i)
        + h' (N + 1) * (∑ i ∈ Finset.Icc 1 N, a i)
      = ∑ j ∈ Finset.Icc 1 N, h' j * a j := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    linear_combination ih

open SupplyChainTheory in
theorem solution (N : ℕ) (h' I' IT : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 N, echelonHolding N h' j * echelonOnHand I' IT j
      = ∑ j ∈ Finset.Icc 1 N, h' j * (I' j + if j = 1 then 0 else IT (j - 1)) := by
  unfold echelonHolding echelonOnHand
  cases N with
  | zero => simp
  | succ M =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    have hcongr : ∑ j ∈ Finset.Icc 1 M,
        (h' j - if j < M + 1 then h' (j + 1) else 0) *
          ∑ i ∈ Finset.Icc 1 j, (I' i + if i = 1 then 0 else IT (i - 1))
        = ∑ j ∈ Finset.Icc 1 M, (h' j - h' (j + 1)) *
          ∑ i ∈ Finset.Icc 1 j, (I' i + if i = 1 then 0 else IT (i - 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < M + 1 := by
        rw [Finset.mem_Icc] at hj
        omega
      rw [if_pos hj']
    have hab := sct_abel_9138e353 h' (fun i => I' i + if i = 1 then 0 else IT (i - 1)) M
    rw [hcongr, if_neg (by omega : ¬ (M + 1 < M + 1)),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    linear_combination hab
