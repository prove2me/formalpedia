-- Prove2me | solution 1 for SuttonBartoRL.FiniteMDP.bellman_equation_stateValue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:36:20.656294+00:00
-- url     : https://prove2.me/submissions/b9225d28-c37c-4c0a-ac16-81993bbf633f

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

set_option autoImplicit false

namespace P2Md297f33d

open SuttonBartoRL.FiniteMDP

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

lemma pT_nonneg (M : MDP S A) (π : Policy S A) (s s' : S) :
    0 ≤ policyTrans M π s s' := by
  unfold policyTrans MDP.trans
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (π.nonneg s a) (Finset.sum_nonneg fun r _ => M.p_nonneg _ _ _ _)

lemma pT_rowsum (M : MDP S A) (π : Policy S A) (s : S) :
    ∑ s', policyTrans M π s s' = 1 := by
  unfold policyTrans MDP.trans
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.p_sum, mul_one, π.sum_one]

lemma eRA_succ (M : MDP S A) (π : Policy S A) (k : ℕ) (s : S) :
    expectedRewardAt M π (k + 1) s =
      ∑ s', policyTrans M π s s' * expectedRewardAt M π k s' := by
  unfold expectedRewardAt
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

lemma eRA_bound (M : MDP S A) (π : Policy S A) (k : ℕ) (s : S) :
    |expectedRewardAt M π k s| ≤ ∑ t, |policyReward M π t| := by
  induction k generalizing s with
  | zero =>
    simp only [expectedRewardAt, pow_zero, Matrix.one_mulVec]
    exact Finset.single_le_sum (f := fun t => |policyReward M π t|)
      (fun t _ => abs_nonneg _) (Finset.mem_univ s)
  | succ k ih =>
    rw [eRA_succ]
    calc _ ≤ ∑ t, |policyTrans M π s t * expectedRewardAt M π k t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, policyTrans M π s t * ∑ t, |policyReward M π t| := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [abs_mul, abs_of_nonneg (pT_nonneg M π s t)]
          exact mul_le_mul_of_nonneg_left (ih t) (pT_nonneg M π s t)
      _ = ∑ t, |policyReward M π t| := by rw [← Finset.sum_mul, pT_rowsum, one_mul]

lemma summ (M : MDP S A) (π : Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
    (h1 : γ < 1) (s : S) : Summable (fun k : ℕ => γ ^ k * expectedRewardAt M π k s) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one h0 h1).mul_right (∑ t, |policyReward M π t|)) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
  exact mul_le_mul_of_nonneg_left (eRA_bound M π k s) (pow_nonneg h0 k)

lemma key (M : MDP S A) (π : Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
    (h1 : γ < 1) (s : S) :
    stateValue M γ π s =
      policyReward M π s + γ * ∑ s', policyTrans M π s s' * stateValue M γ π s' := by
  unfold stateValue
  rw [(summ M π γ h0 h1 s).tsum_eq_zero_add]
  have h00 : γ ^ 0 * expectedRewardAt M π 0 s = policyReward M π s := by
    simp [expectedRewardAt]
  rw [h00]
  congr 1
  have hk : ∀ k : ℕ, γ ^ (k + 1) * expectedRewardAt M π (k + 1) s =
      γ * ∑ s', policyTrans M π s s' * (γ ^ k * expectedRewardAt M π k s') := by
    intro k
    rw [eRA_succ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  simp_rw [hk]
  rw [tsum_mul_left, Summable.tsum_finsetSum]
  · simp_rw [tsum_mul_left]
  · intro t _
    exact (summ M π γ h0 h1 t).mul_left _

lemma rhs_eq (M : MDP S A) (π : Policy S A) (γ : ℝ) (v : S → ℝ)
    (s : S) :
    ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s') =
      policyReward M π s + γ * ∑ s', policyTrans M π s s' * v s' := by
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
  simp only [policyTrans, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ => ?_
  ring

end P2Md297f33d

open SuttonBartoRL.FiniteMDP in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) :
    stateValue M γ π s =
      ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * stateValue M γ π s') := by
  rw [P2Md297f33d.rhs_eq]
  exact P2Md297f33d.key M π γ hγ0 hγ1 s
