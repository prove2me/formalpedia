-- Prove2me | solution 1 for SuttonBartoRL.EpsSoft.eps_greedy_improvement
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:28:36.391923+00:00
-- url     : https://prove2.me/submissions/541e9a42-d9ed-4832-92cd-bae3ad7fe2f1

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_EpsSoftPolicies

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P2M851767d8

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

/-- one-step lookahead -/
noncomputable def Q (M : MDP S A) (γ : ℝ) (u : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * u s')

lemma rhs_eq (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (v : S → ℝ)
    (s : S) :
    ∑ a, π.prob s a * Q M γ v s a =
      policyReward M π s + γ * ∑ s', policyTrans M π s s' * v s' := by
  unfold Q
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
    stateValue M γ π s = ∑ a, π.prob s a * Q M γ (stateValue M γ π) s a := by
  rw [rhs_eq]
  exact key M π γ h0 h1 s

/-- comparison principle -/
lemma cmp (M : MDP S A) (σ : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (h0 : 0 ≤ γ)
    (h1 : γ < 1) (u w : S → ℝ)
    (h : ∀ s, u s - ∑ a, σ.prob s a * Q M γ u s a ≤ w s - ∑ a, σ.prob s a * Q M γ w s a) :
    ∀ s, u s ≤ w s := by
  by_contra hc
  push_neg at hc
  obtain ⟨s₁, hs₁⟩ := hc
  haveI : Nonempty S := ⟨s₁⟩
  obtain ⟨s₀, hs₀⟩ := Finite.exists_max (fun s => u s - w s)
  have hm : 0 < u s₀ - w s₀ := lt_of_lt_of_le (by linarith) (hs₀ s₁)
  have hstep := h s₀
  rw [rhs_eq, rhs_eq] at hstep
  have hle : ∑ t, policyTrans M σ s₀ t * u t - ∑ t, policyTrans M σ s₀ t * w t ≤
      u s₀ - w s₀ := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ t, (policyTrans M σ s₀ t * u t - policyTrans M σ s₀ t * w t)
        ≤ ∑ t, policyTrans M σ s₀ t * (u s₀ - w s₀) := Finset.sum_le_sum fun t _ => by
          rw [← mul_sub]
          exact mul_le_mul_of_nonneg_left (hs₀ t) (pT_nonneg M σ s₀ t)
      _ = u s₀ - w s₀ := by rw [← Finset.sum_mul, pT_rowsum, one_mul]
  have key2 : u s₀ - w s₀ ≤
      γ * (∑ t, policyTrans M σ s₀ t * u t - ∑ t, policyTrans M σ s₀ t * w t) := by
    linarith
  have := mul_le_mul_of_nonneg_left hle h0
  nlinarith

variable [DecidableEq A] [Nonempty A]

lemma greedy_le (ε : ℝ) (σ τ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) (q : A → ℝ) (g : A)
    (hq : ∀ a, q a ≤ q g) (hσ : IsEpsSoft ε σ)
    (hτ : ∀ a, τ.prob s a =
      if a = g then 1 - ε + ε / (Fintype.card A : ℝ) else ε / (Fintype.card A : ℝ)) :
    ∑ a, σ.prob s a * q a ≤ ∑ a, τ.prob s a * q a := by
  set c := ε / (Fintype.card A : ℝ) with hc
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := A)).ne'
  have hnc : (Fintype.card A : ℝ) * c = ε := by rw [hc]; field_simp
  have h1 : ∑ a, σ.prob s a * q a ≤ ∑ a, ((σ.prob s a - c) * q g + c * q a) :=
    Finset.sum_le_sum fun a _ => by
      have := mul_le_mul_of_nonneg_left (hq a) (show 0 ≤ σ.prob s a - c by linarith [hσ s a])
      linarith
  have h2 : ∑ a, ((σ.prob s a - c) * q g + c * q a) = (1 - ε) * q g + c * ∑ a, q a := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, σ.sum_one,
      ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hnc]
  have h3 : ∑ a, τ.prob s a * q a = (1 - ε) * q g + c * ∑ a, q a := by
    have : ∀ a, τ.prob s a * q a = c * q a + (if a = g then (1 - ε) * q a else 0) := by
      intro a
      rw [hτ a]
      split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ g, ← Finset.mul_sum]
    simp only [Finset.mem_univ, if_true]
    ring
  linarith

end P2M851767d8

open SuttonBartoRL.EpsSoft in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (π π' : SuttonBartoRL.FiniteMDP.Policy S A) (hπ : IsEpsSoft ε π)
    (hπ' : IsEpsGreedy M γ ε π π') :
    (∀ s, stateValue M γ π s ≤ stateValue M γ π' s) ∧
      ((∀ s, stateValue M γ π' s = stateValue M γ π s) →
        IsOptimalAmongEpsSoft M γ ε π' ∧ IsOptimalAmongEpsSoft M γ ε π) := by
  obtain ⟨g, hg, hpr⟩ := hπ'
  have hQ : ∀ s a, actionValue M γ π s a = P2M851767d8.Q M γ (stateValue M γ π) s a :=
    fun _ _ => rfl
  -- greedy dominance for any eps-soft policy
  have hdom : ∀ σ : SuttonBartoRL.FiniteMDP.Policy S A, IsEpsSoft ε σ → ∀ s,
      ∑ a, σ.prob s a * P2M851767d8.Q M γ (stateValue M γ π) s a ≤
        ∑ a, π'.prob s a * P2M851767d8.Q M γ (stateValue M γ π) s a := by
    intro σ hσ s
    exact P2M851767d8.greedy_le ε σ π' s _ (g s) (fun a => by rw [← hQ, ← hQ]; exact hg s a)
      hσ (hpr s)
  have hsoft' : IsEpsSoft ε π' := by
    intro s a
    rw [hpr s a]
    split_ifs
    · linarith
    · exact le_refl _
  refine ⟨?_, ?_⟩
  · refine P2M851767d8.cmp M π' γ hγ0 hγ1 _ _ fun s => ?_
    have e1 := P2M851767d8.bellman M π γ hγ0 hγ1 s
    have e2 := P2M851767d8.bellman M π' γ hγ0 hγ1 s
    have := hdom π hπ s
    linarith
  · intro heq
    have hfun : stateValue M γ π' = stateValue M γ π := funext heq
    have hopt : ∀ π'' : SuttonBartoRL.FiniteMDP.Policy S A, IsEpsSoft ε π'' → ∀ s,
        stateValue M γ π'' s ≤ stateValue M γ π s := by
      intro π'' h''
      refine P2M851767d8.cmp M π'' γ hγ0 hγ1 _ _ fun s => ?_
      have e1 := P2M851767d8.bellman M π'' γ hγ0 hγ1 s
      have e2 := P2M851767d8.bellman M π' γ hγ0 hγ1 s
      rw [hfun] at e2
      have := hdom π'' h'' s
      linarith
    refine ⟨⟨hsoft', fun π'' h'' s => ?_⟩, ⟨hπ, hopt⟩⟩
    rw [heq s]
    exact hopt π'' h'' s
