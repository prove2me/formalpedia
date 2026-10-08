-- Prove2me | solution 1 for SuttonBartoRL.AverageReward.steady_state_is_stationary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:13:45.568856+00:00
-- url     : https://prove2.me/submissions/e1525472-5952-4bdd-bbd5-a59c5a961bb1

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

open Filter Topology

namespace SuttonBartoRL.AverageReward.Aaba67e5Aux

open SuttonBartoRL.AverageReward

theorem trans_nonneg {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] (M : MDP S A)
    (s : S) (a : A) (s' : S) : 0 ≤ M.trans s a s' := by
  unfold MDP.trans
  exact Finset.sum_nonneg (fun r _ => M.p_nonneg s a s' r)

theorem trans_sum {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] (M : MDP S A)
    (s : S) (a : A) : ∑ s', M.trans s a s' = 1 := by
  unfold MDP.trans
  exact M.p_sum s a

theorem pt_nonneg {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] (M : MDP S A)
    (π : SuttonBartoRL.FiniteMDP.Policy S A) (s s' : S) : 0 ≤ M.policyTrans π s s' := by
  unfold MDP.policyTrans
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (π.nonneg s a) (trans_nonneg M s a s'))

theorem pt_rowsum {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] (M : MDP S A)
    (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) : ∑ s', M.policyTrans π s s' = 1 := by
  unfold MDP.policyTrans
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, trans_sum, mul_one]
  exact π.sum_one s

theorem pow_nonneg' {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] (M : MDP S A)
    (π : SuttonBartoRL.FiniteMDP.Policy S A) (t : ℕ) (s s' : S) :
    0 ≤ (M.policyTrans π ^ t) s s' := by
  induction t generalizing s' with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (ih x) (pt_nonneg M π x s'))

theorem pow_rowsum {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] (M : MDP S A)
    (π : SuttonBartoRL.FiniteMDP.Policy S A) (t : ℕ) (s : S) :
    ∑ s', (M.policyTrans π ^ t) s s' = 1 := by
  induction t with
  | zero =>
    simp [Matrix.one_apply]
  | succ n ih =>
    simp_rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, pt_rowsum, mul_one]
    exact ih

end SuttonBartoRL.AverageReward.Aaba67e5Aux

open Filter Topology SuttonBartoRL.AverageReward in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ)
    (hμ : ∀ s₀ s, Tendsto (fun t : ℕ => M.stateDist π s₀ t s) atTop (𝓝 (μ s))) :
    IsStationaryDist M π μ := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact ge_of_tendsto' (hμ s₀ s) (fun t => Aaba67e5Aux.pow_nonneg' M π t s₀ s)
  · have h := tendsto_finsetSum (Finset.univ : Finset S) (fun s _ => hμ s₀ s)
    have hc : (fun t : ℕ => ∑ s, M.stateDist π s₀ t s) = fun _ => (1 : ℝ) := by
      funext t
      exact Aaba67e5Aux.pow_rowsum M π t s₀
    rw [hc] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  · intro s'
    have h1 : Tendsto (fun t : ℕ => M.stateDist π s₀ (t + 1) s') atTop (𝓝 (μ s')) :=
      (hμ s₀ s').comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun t : ℕ => ∑ s, M.stateDist π s₀ t s * M.policyTrans π s s') atTop
        (𝓝 (∑ s, μ s * M.policyTrans π s s')) :=
      tendsto_finsetSum _ (fun s _ => (hμ s₀ s).mul_const _)
    have he : (fun t : ℕ => M.stateDist π s₀ (t + 1) s') =
        fun t => ∑ s, M.stateDist π s₀ t s * M.policyTrans π s s' := by
      funext t
      unfold MDP.stateDist
      rw [pow_succ, Matrix.mul_apply]
    rw [he] at h1
    exact tendsto_nhds_unique h2 h1
