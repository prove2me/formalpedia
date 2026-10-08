-- Prove2me | solution 1 for SuttonBartoRL.FiniteMDP.stateValue_shiftRewards
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:07:47.997135+00:00
-- url     : https://prove2.me/submissions/8b12cd90-62e7-4114-a0dc-926fe1352f01

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

open SuttonBartoRL.FiniteMDP in
theorem pbb25_trans_nonneg {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (s : S) (a : A) (s' : S) : 0 ≤ M.trans s a s' :=
  Finset.sum_nonneg fun r _ => M.p_nonneg s a s' r

open SuttonBartoRL.FiniteMDP in
theorem pbb25_trans_sum {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (s : S) (a : A) : ∑ s', M.trans s a s' = 1 :=
  M.p_sum s a

open SuttonBartoRL.FiniteMDP in
theorem pbb25_rowsum {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : Policy S A) (s : S) : ∑ s', policyTrans M π s s' = 1 := by
  simp only [policyTrans]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, pbb25_trans_sum, mul_one]
  exact π.sum_one s

open SuttonBartoRL.FiniteMDP in
theorem pbb25_bound {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
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
      Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg s a) (pbb25_trans_nonneg M s a s')
    have hPs : ∑ s', policyTrans M π s s' = 1 := pbb25_rowsum M π s
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
theorem pbb25_summable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) :
    Summable (fun k : ℕ => γ ^ k * expectedRewardAt M π k s) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ t, |policyReward M π t|)) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 k)]
  exact mul_le_mul_of_nonneg_left (pbb25_bound M π k s) (pow_nonneg hγ0 k)

open SuttonBartoRL.FiniteMDP in
theorem pbb25_trans_shift {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (c : ℝ) (s : S) (a : A) (s' : S) :
    (M.shiftRewards c).trans s a s' = M.trans s a s' := by
  simp [MDP.trans, MDP.shiftRewards, Finset.sum_map]

open SuttonBartoRL.FiniteMDP in
theorem pbb25_expReward_shift {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (c : ℝ) (s : S) (a : A) :
    (M.shiftRewards c).expReward s a = M.expReward s a + c := by
  have h1 : (M.shiftRewards c).expReward s a = ∑ r ∈ M.R, (r + c) * ∑ s', M.p s a s' r := by
    simp [MDP.expReward, MDP.shiftRewards, Finset.sum_map]
  have h2 : ∑ r ∈ M.R, ∑ s', M.p s a s' r = 1 := by
    rw [Finset.sum_comm]; exact M.p_sum s a
  rw [h1, MDP.expReward]
  simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, h2, mul_one]

open SuttonBartoRL.FiniteMDP in
theorem pbb25_policyTrans_shift {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (c : ℝ) (π : Policy S A) :
    policyTrans (M.shiftRewards c) π = policyTrans M π := by
  funext s s'
  simp only [policyTrans, pbb25_trans_shift]

open SuttonBartoRL.FiniteMDP in
theorem pbb25_policyReward_shift {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (c : ℝ) (π : Policy S A) :
    policyReward (M.shiftRewards c) π = fun s => policyReward M π s + c := by
  funext s
  simp only [policyReward, pbb25_expReward_shift, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, π.sum_one s, one_mul]

open SuttonBartoRL.FiniteMDP in
theorem pbb25_const {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : Policy S A) (c : ℝ) (k : ℕ) :
    Matrix.mulVec (policyTrans M π ^ k) (fun _ => c) = fun _ => c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    funext s
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_mul, pbb25_rowsum M π s, one_mul]

open SuttonBartoRL.FiniteMDP in
theorem pbb25_expectedRewardAt_shift {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (c : ℝ) (π : Policy S A) (k : ℕ) (s : S) :
    expectedRewardAt (M.shiftRewards c) π k s = expectedRewardAt M π k s + c := by
  have h : (fun s => policyReward M π s + c) = policyReward M π + (fun _ => c) := rfl
  simp only [expectedRewardAt, pbb25_policyTrans_shift, pbb25_policyReward_shift, h,
    Matrix.mulVec_add, pbb25_const, Pi.add_apply]

open SuttonBartoRL.FiniteMDP in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (c : ℝ) (π : Policy S A) (s : S) :
    stateValue (M.shiftRewards c) γ π s = stateValue M γ π s + c / (1 - γ) := by
  have hg : Summable (fun k : ℕ => γ ^ k * c) :=
    (summable_geometric_of_lt_one hγ0 hγ1).mul_right c
  have hgs : ∑' k : ℕ, γ ^ k * c = c / (1 - γ) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1, div_eq_mul_inv, mul_comm]
  simp only [stateValue, pbb25_expectedRewardAt_shift, mul_add]
  rw [Summable.tsum_add (pbb25_summable M γ hγ0 hγ1 π s) hg, hgs]
