-- Prove2me | solution 1 for SuttonBartoRL.AverageReward.bellman_equation_discounted
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:56:36.963455+00:00
-- url     : https://prove2.me/submissions/285cb260-3fd6-425a-bb7a-c845d3974cf7

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP

set_option autoImplicit false

namespace P2M9c1f9e1b

open SuttonBartoRL.AverageReward

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

lemma pT_nonneg (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s s' : S) :
    0 ≤ M.policyTrans π s s' := by
  unfold MDP.policyTrans MDP.trans
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (π.nonneg s a) (Finset.sum_nonneg fun r _ => M.p_nonneg _ _ _ _)

lemma pT_rowsum (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    ∑ s', M.policyTrans π s s' = 1 := by
  unfold MDP.policyTrans MDP.trans
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.p_sum, mul_one, π.sum_one]

lemma eRA_succ (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) (s : S) :
    M.expectedRewardAt π (k + 1) s =
      ∑ s', M.policyTrans π s s' * M.expectedRewardAt π k s' := by
  unfold MDP.expectedRewardAt
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

lemma eRA_bound (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) (s : S) :
    |M.expectedRewardAt π k s| ≤ ∑ t, |M.policyReward π t| := by
  induction k generalizing s with
  | zero =>
    simp only [MDP.expectedRewardAt, pow_zero, Matrix.one_mulVec]
    exact Finset.single_le_sum (f := fun t => |M.policyReward π t|)
      (fun t _ => abs_nonneg _) (Finset.mem_univ s)
  | succ k ih =>
    rw [eRA_succ]
    calc _ ≤ ∑ t, |M.policyTrans π s t * M.expectedRewardAt π k t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, M.policyTrans π s t * ∑ t, |M.policyReward π t| := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [abs_mul, abs_of_nonneg (pT_nonneg M π s t)]
          exact mul_le_mul_of_nonneg_left (ih t) (pT_nonneg M π s t)
      _ = ∑ t, |M.policyReward π t| := by rw [← Finset.sum_mul, pT_rowsum, one_mul]

lemma summ (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
    (h1 : γ < 1) (s : S) : Summable (fun k : ℕ => γ ^ k * M.expectedRewardAt π k s) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one h0 h1).mul_right (∑ t, |M.policyReward π t|)) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
  exact mul_le_mul_of_nonneg_left (eRA_bound M π k s) (pow_nonneg h0 k)

lemma key (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
    (h1 : γ < 1) (s : S) :
    M.stateValue γ π s =
      M.policyReward π s + γ * ∑ s', M.policyTrans π s s' * M.stateValue γ π s' := by
  unfold MDP.stateValue
  rw [(summ M π γ h0 h1 s).tsum_eq_zero_add]
  have h00 : γ ^ 0 * M.expectedRewardAt π 0 s = M.policyReward π s := by
    simp [MDP.expectedRewardAt]
  rw [h00]
  congr 1
  have hk : ∀ k : ℕ, γ ^ (k + 1) * M.expectedRewardAt π (k + 1) s =
      γ * ∑ s', M.policyTrans π s s' * (γ ^ k * M.expectedRewardAt π k s') := by
    intro k
    rw [eRA_succ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  simp_rw [hk]
  rw [tsum_mul_left, Summable.tsum_finsetSum]
  · simp_rw [tsum_mul_left]
  · intro t _
    exact (summ M π γ h0 h1 t).mul_left _

lemma rhs_eq (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (v : S → ℝ)
    (s : S) :
    ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s') =
      M.policyReward π s + γ * ∑ s', M.policyTrans π s s' * v s' := by
  have ha : ∀ a, ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s') =
      M.expReward s a + γ * ∑ s', M.trans s a s' * v s' := by
    intro a
    simp only [mul_add, Finset.sum_add_distrib, MDP.expReward, MDP.trans]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
  simp_rw [ha, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [MDP.policyTrans, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ => ?_
  ring

end P2M9c1f9e1b

open SuttonBartoRL.AverageReward in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    M.stateValue γ π s =
      ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * M.stateValue γ π s') := by
  rw [P2M9c1f9e1b.rhs_eq]
  exact P2M9c1f9e1b.key M π γ hγ0 hγ1 s
