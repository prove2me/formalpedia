-- Prove2me | solution 1 for PandoraBO.Private20261023.optimal_policy_subsequence_limits
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:27.249989+00:00
-- url     : https://prove2.me/submissions/8f195693-f274-4c05-9dd4-58bb137433d1

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_optimal_policy_cost_reward_monotonicity
import Mathlib.Topology.Order.MonotoneConvergence

/-! A deterministic choice of optimal policy at each multiplier makes cost
and reward monotone along monotone multiplier sequences, including plateaus.+A convergent cofinal subsequence then determines the full expectation limit. -/

set_option autoImplicit false
open PandoraBO Filter Topology

namespace PandoraBO.Private20261023.SubsequenceLifting

theorem monotone_real_subsequence_limit (f : ℕ → ℝ) (a : ℝ)
    (hf : Monotone f ∨ Antitone f) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => f (φ k)) atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) := by
  rcases hf with hmono | hanti
  · exact (tendsto_iff_tendsto_subseq_of_monotone hmono hφ.tendsto_atTop).2 hlim
  · exact (tendsto_iff_tendsto_subseq_of_antitone hanti hφ.tendsto_atTop).2 hlim

theorem optimal_expectation_sequences_monotone {n : ℕ} (M : Instance n)
    (multipliers : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ multipliers k)
    (policies : ℕ → Policy n)
    (hopt : ∀ k, optimal M (multipliers k) (policies k))
    (hsame : ∀ j k, multipliers j = multipliers k → policies j = policies k)
    (hmono : Monotone multipliers ∨ Antitone multipliers) :
    (Monotone (fun k => expectedCost M (policies k)) ∨
      Antitone (fun k => expectedCost M (policies k))) ∧
    (Monotone (fun k => expectedReward M (policies k)) ∨
      Antitone (fun k => expectedReward M (policies k))) := by
  have hcompare : ∀ i j, multipliers i ≤ multipliers j →
      expectedCost M (policies j) ≤ expectedCost M (policies i) ∧
        expectedReward M (policies j) ≤ expectedReward M (policies i) := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hlt | heq
    · exact PandoraBO.Private20261023.optimal_policy_cost_reward_monotonicity M
        (multipliers i) (multipliers j) (hnonneg i) hlt
        (policies i) (policies j) (hopt i) (hopt j)
    · rw [hsame i j heq]
      exact ⟨le_rfl, le_rfl⟩
  rcases hmono with hinc | hdec
  · exact ⟨Or.inr (fun i j hij => (hcompare i j (hinc hij)).1),
      Or.inr (fun i j hij => (hcompare i j (hinc hij)).2)⟩
  · exact ⟨Or.inl (fun i j hij => (hcompare j i (hdec hij)).1),
      Or.inl (fun i j hij => (hcompare j i (hdec hij)).2)⟩

end PandoraBO.Private20261023.SubsequenceLifting

theorem solution {n : ℕ} (M : Instance n)
    (multipliers : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ multipliers k)
    (policies : ℕ → Policy n)
    (hopt : ∀ k, optimal M (multipliers k) (policies k))
    (hsame : ∀ j k, multipliers j = multipliers k → policies j = policies k)
    (hmono : Monotone multipliers ∨ Antitone multipliers)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (costLimit rewardLimit : ℝ)
    (hcost : Tendsto (fun k => expectedCost M (policies (φ k))) atTop (𝓝 costLimit))
    (hreward : Tendsto (fun k => expectedReward M (policies (φ k))) atTop (𝓝 rewardLimit)) :
    Tendsto (fun k => expectedCost M (policies k)) atTop (𝓝 costLimit) ∧
      Tendsto (fun k => expectedReward M (policies k)) atTop (𝓝 rewardLimit) := by
  obtain ⟨hcostmono, hrewardmono⟩ :=
    PandoraBO.Private20261023.SubsequenceLifting.optimal_expectation_sequences_monotone M
      multipliers hnonneg policies hopt hsame hmono
  exact ⟨PandoraBO.Private20261023.SubsequenceLifting.monotone_real_subsequence_limit _ _
    hcostmono φ hφ hcost,
    PandoraBO.Private20261023.SubsequenceLifting.monotone_real_subsequence_limit _ _
      hrewardmono φ hφ hreward⟩
