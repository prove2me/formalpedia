-- Prove2me | solution 1 for SuttonBartoRL.EpsSoft.policy_improvement_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:23:39.897038+00:00
-- url     : https://prove2.me/submissions/35c0b6f8-16ce-4f67-ac17-e2cd251d0d85

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_ValueFunctions


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P2M13ce78d4

open SuttonBartoRL.EpsSoft

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

lemma pT_nonneg (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s s' : S) :
    0 ≤ policyTrans M π s s' := by
  unfold policyTrans MDP.trans
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (π.nonneg s a) (Finset.sum_nonneg fun r _ => M.p_nonneg _ _ _ _)

lemma pT_rowsum (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    ∑ s', policyTrans M π s s' = 1 := by
  unfold policyTrans MDP.trans
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.p_sum, mul_one, π.sum_one]

lemma eRA_succ (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) (s : S) :
    expectedRewardAt M π (k + 1) s =
      ∑ s', policyTrans M π s s' * expectedRewardAt M π k s' := by
  unfold expectedRewardAt
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

lemma eRA_bound (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) (s : S) :
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

lemma summ (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
    (h1 : γ < 1) (s : S) : Summable (fun k : ℕ => γ ^ k * expectedRewardAt M π k s) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one h0 h1).mul_right (∑ t, |policyReward M π t|)) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
  exact mul_le_mul_of_nonneg_left (eRA_bound M π k s) (pow_nonneg h0 k)

lemma key (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
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

lemma rhs_eq (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (v : S → ℝ)
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

lemma bellman (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
    (h1 : γ < 1) (s : S) :
    stateValue M γ π s = ∑ a, π.prob s a * actionValue M γ π s a := by
  unfold actionValue
  rw [rhs_eq M π γ (fun s' => stateValue M γ π s') s]
  exact key M π γ h0 h1 s


noncomputable def Q (M : MDP S A) (γ : ℝ) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s')

lemma Q_mono (M : MDP S A) (γ : ℝ) (h0 : 0 ≤ γ) (u w : S → ℝ) (h : ∀ s, u s ≤ w s)
    (s : S) (a : A) : Q M γ u s a ≤ Q M γ w s a := by
  unfold Q
  refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun r _ => ?_
  exact mul_le_mul_of_nonneg_left
    (by linarith [mul_le_mul_of_nonneg_left (h t) h0]) (M.p_nonneg _ _ _ _)

lemma Q_add_const (M : MDP S A) (γ : ℝ) (w : S → ℝ) (c : ℝ) (s : S) (a : A) :
    Q M γ (fun t => w t + c) s a = Q M γ w s a + γ * c := by
  unfold Q
  have : ∀ t, ∑ r ∈ M.R, M.p s a t r * (r + γ * (w t + c)) =
      ∑ r ∈ M.R, M.p s a t r * (r + γ * w t) + (∑ r ∈ M.R, M.p s a t r) * (γ * c) := by
    intro t
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, M.p_sum, one_mul]

lemma PQ_mono (M : MDP S A) (γ : ℝ) (h0 : 0 ≤ γ) (π : SuttonBartoRL.FiniteMDP.Policy S A)
    (u w : S → ℝ) (h : ∀ s, u s ≤ w s) (s : S) :
    ∑ a, π.prob s a * Q M γ u s a ≤ ∑ a, π.prob s a * Q M γ w s a :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (Q_mono M γ h0 u w h s a) (π.nonneg s a)

lemma PQ_add_const (M : MDP S A) (γ : ℝ) (π : SuttonBartoRL.FiniteMDP.Policy S A)
    (w : S → ℝ) (c : ℝ) (s : S) :
    ∑ a, π.prob s a * Q M γ (fun t => w t + c) s a = ∑ a, π.prob s a * Q M γ w s a + γ * c := by
  simp_rw [Q_add_const, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, π.sum_one, one_mul]

lemma bellQ (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
    (h1 : γ < 1) (s : S) :
    stateValue M γ π s = ∑ a, π.prob s a * Q M γ (stateValue M γ π) s a :=
  bellman M π γ h0 h1 s

lemma main (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π π' : SuttonBartoRL.FiniteMDP.Policy S A)
    (h : ∀ s, stateValue M γ π s ≤ ∑ a, π'.prob s a * actionValue M γ π s a) (s : S) :
    stateValue M γ π s ≤ stateValue M γ π' s := by
  set v := stateValue M γ π with hv
  set w := stateValue M γ π' with hw
  by_contra hcon
  push Not at hcon
  have : Nonempty S := ⟨s⟩
  obtain ⟨x, hx⟩ := Finite.exists_max (fun t => v t - w t)
  set m := v x - w x with hm
  have hmpos : 0 < m := by
    have := hx s
    linarith
  have hle : ∀ t, v t ≤ w t + m := by
    intro t
    have := hx t
    linarith
  have h1 : v x ≤ ∑ a, π'.prob x a * Q M γ v x a := h x
  have h2 := PQ_mono M γ hγ0 π' _ _ hle x
  rw [PQ_add_const] at h2
  have h3 : w x = ∑ a, π'.prob x a * Q M γ w x a := bellQ M π' γ hγ0 hγ1 x
  have h4 : γ * m < m := mul_lt_of_lt_one_left hmpos hγ1
  linarith

end P2M13ce78d4

open SuttonBartoRL.EpsSoft in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π π' : SuttonBartoRL.FiniteMDP.Policy S A)
    (h : ∀ s, stateValue M γ π s ≤ ∑ a, π'.prob s a * actionValue M γ π s a) :
    (∀ s, stateValue M γ π s ≤ stateValue M γ π' s) ∧
      (∀ s, stateValue M γ π s < ∑ a, π'.prob s a * actionValue M γ π s a →
        stateValue M γ π s < stateValue M γ π' s) := by
  have hle := P2M13ce78d4.main M γ hγ0 hγ1 π π' h
  refine ⟨hle, fun s hs => ?_⟩
  have h1 := P2M13ce78d4.PQ_mono M γ hγ0 π' _ _ hle s
  have h2 := P2M13ce78d4.bellQ M π' γ hγ0 hγ1 s
  have h3 : ∑ a, π'.prob s a * actionValue M γ π s a =
      ∑ a, π'.prob s a * P2M13ce78d4.Q M γ (stateValue M γ π) s a := rfl
  linarith
