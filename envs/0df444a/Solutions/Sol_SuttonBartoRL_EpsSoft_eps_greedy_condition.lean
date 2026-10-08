-- Prove2me | solution 1 for SuttonBartoRL.EpsSoft.eps_greedy_condition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:46:54.699987+00:00
-- url     : https://prove2.me/submissions/62685478-14c9-432d-8bf9-f780046c8b2d

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_EpsSoftPolicies

set_option autoImplicit false

namespace P2M8dbd8e11

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

end P2M8dbd8e11

open SuttonBartoRL.EpsSoft in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (π π' : SuttonBartoRL.FiniteMDP.Policy S A) (hπ : IsEpsSoft ε π) (hπ' : IsEpsGreedy M γ ε π π') :
    ∀ s, (∑ a, π'.prob s a * actionValue M γ π s a =
        ε / (Fintype.card A : ℝ) * ∑ a, actionValue M γ π s a +
          (1 - ε) * Finset.univ.sup' Finset.univ_nonempty (fun a => actionValue M γ π s a)) ∧
      stateValue M γ π s ≤ ∑ a, π'.prob s a * actionValue M γ π s a := by
  intro s
  obtain ⟨g, hg, hp⟩ := hπ'
  set q : A → ℝ := fun a => actionValue M γ π s a with hq
  set c : ℝ := ε / (Fintype.card A : ℝ) with hc
  have hmax : Finset.univ.sup' Finset.univ_nonempty q = q (g s) :=
    le_antisymm (Finset.sup'_le _ _ fun a _ => hg s a) (Finset.le_sup' q (Finset.mem_univ _))
  have hid : ∑ a, π'.prob s a * q a = c * ∑ a, q a + (1 - ε) * q (g s) := by
    have : ∀ a, π'.prob s a * q a = c * q a + (if a = g s then (1 - ε) * q a else 0) := by
      intro a
      rw [hp s a]
      split_ifs <;> ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_ite_eq']
    simp
  have hidq : ∑ a, π'.prob s a * actionValue M γ π s a =
      c * ∑ a, actionValue M γ π s a + (1 - ε) * q (g s) := hid
  refine ⟨?_, ?_⟩
  · rw [hidq]
    show _ = c * _ + (1 - ε) * Finset.univ.sup' Finset.univ_nonempty q
    rw [hmax]
  · rw [P2M8dbd8e11.bellman M π γ hγ0 hγ1 s, hidq]
    have hcard : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    have hsum : ∑ a, (π.prob s a - c) = 1 - ε := by
      rw [Finset.sum_sub_distrib, π.sum_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        hc]
      field_simp
    have h1 : ∑ a, π.prob s a * q a = ∑ a, (π.prob s a - c) * q a + c * ∑ a, q a := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have h2 : ∑ a, (π.prob s a - c) * q a ≤ ∑ a, (π.prob s a - c) * q (g s) :=
      Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hg s a) (sub_nonneg.mpr (hπ s a))
    rw [← Finset.sum_mul, hsum] at h2
    show ∑ a, π.prob s a * q a ≤ _
    rw [h1]
    linarith
