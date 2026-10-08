-- Prove2me | solution 1 for SuttonBartoRL.FiniteMDP.actionValue_eq_lookahead
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:25:47.20633+00:00
-- url     : https://prove2.me/submissions/2e511dee-f928-433a-b580-21e40a12f87d

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

open SuttonBartoRL.FiniteMDP in
theorem p2m4aaa_trans_nonneg {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (s : S) (a : A) (s' : S) : 0 ≤ M.trans s a s' :=
  Finset.sum_nonneg fun r _ => M.p_nonneg s a s' r

open SuttonBartoRL.FiniteMDP in
theorem p2m4aaa_trans_sum {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (s : S) (a : A) : ∑ s', M.trans s a s' = 1 :=
  M.p_sum s a

open SuttonBartoRL.FiniteMDP in
theorem p2m4aaa_bound {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : Policy S A) (k : ℕ) (s : S) :
    |expectedRewardAt M π k s| ≤ ∑ t, |policyReward M π t| := by
  induction k generalizing s with
  | zero =>
    simp only [expectedRewardAt, pow_zero, Matrix.one_mulVec]
    exact Finset.single_le_sum (f := fun t => |policyReward M π t|)
      (fun t _ => abs_nonneg _) (Finset.mem_univ s)
  | succ k ih =>
    have hstep : expectedRewardAt M π (k + 1) s
        = ∑ s', policyTrans M π s s' * expectedRewardAt M π k s' := by
      simp only [expectedRewardAt]
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      rfl
    have hP : ∀ s', 0 ≤ policyTrans M π s s' := fun s' =>
      Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg s a) (p2m4aaa_trans_nonneg M s a s')
    have hPs : ∑ s', policyTrans M π s s' = 1 := by
      simp only [policyTrans]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, p2m4aaa_trans_sum, mul_one]
      exact π.sum_one s
    rw [hstep]
    calc |∑ s', policyTrans M π s s' * expectedRewardAt M π k s'|
        ≤ ∑ s', |policyTrans M π s s' * expectedRewardAt M π k s'| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s', policyTrans M π s s' * |expectedRewardAt M π k s'| := by
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [abs_mul, abs_of_nonneg (hP s')]
      _ ≤ ∑ s', policyTrans M π s s' * ∑ t, |policyReward M π t| :=
          Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (ih s') (hP s')
      _ = ∑ t, |policyReward M π t| := by rw [← Finset.sum_mul, hPs, one_mul]

open SuttonBartoRL.FiniteMDP in
theorem p2m4aaa_summable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) :
    Summable (fun k : ℕ => γ ^ k * expectedRewardAt M π k s) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ t, |policyReward M π t|)) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 k)]
  exact mul_le_mul_of_nonneg_left (p2m4aaa_bound M π k s) (pow_nonneg hγ0 k)

open SuttonBartoRL.FiniteMDP in
theorem p2m4aaa_term {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (π : Policy S A) (s : S) (a : A) (k : ℕ) :
    γ ^ (k + 1) * actionExpectedRewardAt M π s a (k + 1)
      = ∑ s', γ * M.trans s a s' * (γ ^ k * expectedRewardAt M π k s') := by
  rw [actionExpectedRewardAt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  ring

open SuttonBartoRL.FiniteMDP in
theorem p2m4aaa_step {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) (a : A) :
    actionValue M γ π s a = M.expReward s a + ∑ s', γ * M.trans s a s' * stateValue M γ π s' := by
  have hs : ∀ s' ∈ (Finset.univ : Finset S),
      Summable (fun k : ℕ => γ * M.trans s a s' * (γ ^ k * expectedRewardAt M π k s')) :=
    fun s' _ => (p2m4aaa_summable M γ hγ0 hγ1 π s').mul_left _
  have hsum : Summable (fun k : ℕ => γ ^ (k + 1) * actionExpectedRewardAt M π s a (k + 1)) :=
    (summable_sum hs).congr fun k => (p2m4aaa_term M γ π s a k).symm
  have h1 : actionValue M γ π s a = γ ^ 0 * actionExpectedRewardAt M π s a 0
      + ∑' k : ℕ, γ ^ (k + 1) * actionExpectedRewardAt M π s a (k + 1) :=
    tsum_eq_zero_add' hsum
  rw [h1, tsum_congr (p2m4aaa_term M γ π s a), Summable.tsum_finsetSum hs]
  rw [pow_zero, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun s' _ => tsum_mul_left

/- Sutton & Barto, 2nd ed., Exercise 3.19, p. 62 (the book gives no solution): for `0 ≤ γ < 1`,
`q_π(s, a) = E[R_{t+1} + γ v_π(S_{t+1}) | S_t = s, A_t = a] = Σ_{s',r} p(s', r|s, a) [r + γ v_π(s')]`. -/
open SuttonBartoRL.FiniteMDP in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) (a : A) :
    actionValue M γ π s a = ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * stateValue M γ π s') := by
  rw [p2m4aaa_step M γ hγ0 hγ1 π s a]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [MDP.expReward, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  · refine Finset.sum_congr rfl fun s' _ => ?_
    rw [MDP.trans, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
