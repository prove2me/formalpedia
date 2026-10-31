-- Prove2me | solution 1 for TeamDelegation.Optimal.surplus_implies_collusion_proof
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:03:19.691392+00:00
-- url     : https://prove2.me/submissions/91272d09-f04c-46d4-9795-e0e427cf894c

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model
open TeamDelegation.Optimal

theorem solution(P : Params) (hS : P.Standing)
    (C : Costs) (wA wB : ℝ)
    (hmax : SurplusMax P C .deleg wA wB) :
    CollusionProof P C .deleg wA wB := by
  intro μ hμ hcon
  obtain ⟨hA, hB, hor⟩ := hcon
  have hk : ∀ k : State, (∑ x, μ k x * payA P C k x.1 x.2 wA) +
      (∑ x, μ k x * payB P C k x.1 x.2 wB) ≤
      payA P C k (desiredA k) true wA + payB P C k (desiredA k) true wB := by
    intro k
    obtain ⟨h0, h1, _⟩ := hμ k
    rw [← Finset.sum_add_distrib]
    calc ∑ x, (μ k x * payA P C k x.1 x.2 wA + μ k x * payB P C k x.1 x.2 wB)
        ≤ ∑ x, μ k x * (payA P C k (desiredA k) true wA + payB P C k (desiredA k) true wB) := by
          apply Finset.sum_le_sum
          intro x _
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left
            (hmax k x.1 x.2 (by first | trivial | simp [FeasibleA])) (h0 x)
      _ = _ := by rw [← Finset.sum_mul, h1, one_mul]
  have h0 := hk 0
  have h1 := hk 1
  obtain ⟨he, hδ0, hδ1, hr0, hr1, _, _⟩ := hS
  unfold contValueA contValueB avgPayA avgPayB at *
  rcases hor with h | h <;>
    nlinarith [mul_le_mul_of_nonneg_left h0 hr0,
      mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - P.r)]
