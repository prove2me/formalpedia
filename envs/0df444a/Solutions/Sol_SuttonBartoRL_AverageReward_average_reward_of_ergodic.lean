-- Prove2me | solution 1 for SuttonBartoRL.AverageReward.average_reward_of_ergodic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:47:46.02104+00:00
-- url     : https://prove2.me/submissions/00e86ccc-765c-4f65-9f5d-5609724ea88d

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

open Filter Topology

open SuttonBartoRL.AverageReward in
theorem p27c528d2_limit {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ)
    (hμ : ∀ s₀ s, Tendsto (fun t : ℕ => M.stateDist π s₀ t s) atTop (𝓝 (μ s)))
    (s₀ : S) :
    Tendsto (fun t : ℕ => M.expectedRewardAt π t s₀) atTop (𝓝 (avgReward M π μ)) := by
  have hE : ∀ t, M.expectedRewardAt π t s₀ =
      ∑ s, M.stateDist π s₀ t s * M.policyReward π s := by
    intro t
    rfl
  have hA : avgReward M π μ = ∑ s, μ s * M.policyReward π s := by
    unfold avgReward MDP.policyReward MDP.expReward
    refine Finset.sum_congr rfl (fun s _ => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    ring
  simp_rw [hE]
  rw [hA]
  exact tendsto_finsetSum _ (fun s _ => (hμ s₀ s).mul_const _)

open Filter Topology SuttonBartoRL.AverageReward in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ)
    (hμ : ∀ s₀ s, Tendsto (fun t : ℕ => M.stateDist π s₀ t s) atTop (𝓝 (μ s)))
    (s₀ : S) :
    Tendsto (fun t : ℕ => M.expectedRewardAt π t s₀) atTop (𝓝 (avgReward M π μ)) ∧
    Tendsto (fun h : ℕ => (1 / (h : ℝ)) * ∑ t ∈ Finset.range h, M.expectedRewardAt π t s₀)
      atTop (𝓝 (avgReward M π μ)) := by
  have h1 := p27c528d2_limit M π μ hμ s₀
  refine ⟨h1, ?_⟩
  simpa only [one_div] using h1.cesaro
