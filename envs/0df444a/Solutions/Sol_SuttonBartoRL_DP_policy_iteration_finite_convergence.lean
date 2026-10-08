-- Prove2me | solution 1 for SuttonBartoRL.DP.policy_iteration_finite_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:51:14.181763+00:00
-- url     : https://prove2.me/submissions/fd7eec21-93ab-4110-9f19-74b8eb8bfdb4

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P2M2d87508b

open SuttonBartoRL.DP

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


/-- one-step lookahead -/
noncomputable def Q (M : MDP S A) (γ : ℝ) (u : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * u s')

lemma bellman (M : MDP S A) (π : Policy S A) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1) (s : S) :
    stateValue M γ π s =
      ∑ a, π.prob s a * Q M γ (stateValue M γ π) s a := by
  unfold Q
  rw [rhs_eq]
  exact key M π γ h0 h1 s

lemma bellman_det [DecidableEq A] (M : MDP S A) (d : S → A) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1)
    (s : S) :
    stateValue M γ (Policy.ofDet d) s = Q M γ (stateValue M γ (Policy.ofDet d)) s (d s) := by
  rw [bellman M _ γ h0 h1 s]
  simp [Policy.ofDet]

lemma Q_mono (M : MDP S A) (γ : ℝ) (h0 : 0 ≤ γ) (u w : S → ℝ) (h : ∀ s, u s ≤ w s)
    (s : S) (a : A) : Q M γ u s a ≤ Q M γ w s a := by
  unfold Q
  refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun r _ => ?_
  have := mul_le_mul_of_nonneg_left (h t) h0
  exact mul_le_mul_of_nonneg_left (by linarith) (M.p_nonneg _ _ _ _)

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


/-- Bellman optimality operator. -/
noncomputable def Tm [Nonempty A] (M : MDP S A) (γ : ℝ) (u : S → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => Q M γ u s a)


lemma wsum_le (π : Policy S A) (s : S) (f : A → ℝ) (c : ℝ) (h : ∀ a, f a ≤ c) :
    ∑ a, π.prob s a * f a ≤ c := by
  calc ∑ a, π.prob s a * f a ≤ ∑ a, π.prob s a * c :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (π.nonneg s a)
    _ = c := by rw [← Finset.sum_mul, π.sum_one, one_mul]

lemma value_le [Nonempty A] (M : MDP S A) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1) (v : S → ℝ)
    (hfix : ∀ s, Tm M γ v s = v s) (π : Policy S A) (s : S) :
    stateValue M γ π s ≤ v s := by
  set w := stateValue M γ π with hw
  by_contra hcon'
  have hcon := not_le.mp hcon'
  have : Nonempty S := ⟨s⟩
  obtain ⟨x, hx⟩ := Finite.exists_max (fun t => w t - v t)
  set m := w x - v x with hm
  have hmpos : 0 < m := by
    have := hx s
    linarith
  have hle : ∀ t, w t ≤ v t + m := by
    intro t
    have := hx t
    linarith
  have hb := bellman M π γ h0 h1 x
  have hq : ∀ a, Q M γ w x a ≤ v x + γ * m := by
    intro a
    have h2 := Q_mono M γ h0 _ _ hle x a
    rw [Q_add_const] at h2
    have h3 : Q M γ v x a ≤ Tm M γ v x :=
      Finset.le_sup' (fun a => Q M γ v x a) (Finset.mem_univ a)
    rw [hfix] at h3
    linarith
  have h5 := wsum_le π x (fun a => Q M γ w x a) _ hq
  have h4 : γ * m < m := mul_lt_of_lt_one_left hmpos h1
  rw [← hw] at hb
  linarith

lemma actionValue_eq (M : MDP S A) (γ : ℝ) (π : Policy S A) (s : S) (a : A) :
    actionValue M γ π s a = Q M γ (stateValue M γ π) s a := rfl

lemma improve [DecidableEq A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π π' : S → A)
    (h47 : ∀ s, stateValue M γ (Policy.ofDet π) s ≤
      actionValue M γ (Policy.ofDet π) s (π' s)) (s : S) :
    stateValue M γ (Policy.ofDet π) s ≤ stateValue M γ (Policy.ofDet π') s := by
  set v := stateValue M γ (Policy.ofDet π) with hv
  set w := stateValue M γ (Policy.ofDet π') with hw
  by_contra hcon'
  have hcon := not_le.mp hcon'
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
  have h1 : v x ≤ Q M γ v x (π' x) := h47 x
  have h2 : Q M γ v x (π' x) ≤ Q M γ (fun t => w t + m) x (π' x) :=
    Q_mono M γ hγ0 _ _ hle x _
  rw [Q_add_const] at h2
  have h3 : w x = Q M γ w x (π' x) := bellman_det M π' γ hγ0 hγ1 x
  have h4 : γ * m < m := mul_lt_of_lt_one_left hmpos hγ1
  linarith

lemma greedy_step [DecidableEq A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π π' : S → A) (hg : IsGreedy M γ (Policy.ofDet π) π') (s : S) :
    stateValue M γ (Policy.ofDet π) s ≤ stateValue M γ (Policy.ofDet π') s := by
  refine improve M γ hγ0 hγ1 π π' (fun t => ?_) s
  have h := hg t (π t)
  have hb := bellman_det M π γ hγ0 hγ1 t
  exact hb.trans_le h

lemma opt_of_eq [Nonempty A] [DecidableEq A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π π' : S → A) (hg : IsGreedy M γ (Policy.ofDet π) π')
    (heq : ∀ s, stateValue M γ (Policy.ofDet π') s = stateValue M γ (Policy.ofDet π) s) :
    IsOptimalPolicy M γ (Policy.ofDet π) := by
  set v := stateValue M γ (Policy.ofDet π) with hv
  have hfeq : stateValue M γ (Policy.ofDet π') = v := funext heq
  have hfix : ∀ s, Tm M γ v s = v s := by
    intro s
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun a _ => ?_
      have h := hg s a
      simp only [actionValue_eq] at h
      have hb := bellman_det M π' γ hγ0 hγ1 s
      rw [hfeq] at hb
      have : v s = stateValue M γ (Policy.ofDet π') s := (heq s).symm
      linarith
    · have hb := bellman_det M π γ hγ0 hγ1 s
      have h3 : Q M γ v s (π s) ≤ Tm M γ v s :=
        Finset.le_sup' (fun a => Q M γ v s a) (Finset.mem_univ (π s))
      linarith
  intro π'' s
  exact value_le M γ hγ0 hγ1 v hfix π'' s

lemma optVal_of_opt (M : MDP S A) (γ : ℝ) (π : Policy S A) (h : IsOptimalPolicy M γ π) (s : S) :
    stateValue M γ π s = optimalValue M γ s := by
  have : Nonempty (Policy S A) := ⟨π⟩
  unfold optimalValue
  refine le_antisymm ?_ (ciSup_le fun π' => h π' s)
  have hb : BddAbove (Set.range fun π' : Policy S A => stateValue M γ π' s) := by
    refine ⟨stateValue M γ π s, ?_⟩
    rintro _ ⟨π', rfl⟩
    exact h π' s
  exact le_ciSup hb π

end P2M2d87508b

open SuttonBartoRL.DP in
theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πs : ℕ → S → A) (hgreedy : ∀ k, IsGreedy M γ (Policy.ofDet (πs k)) (πs (k + 1))) :
    (∀ k, IsOptimalPolicy M γ (Policy.ofDet (πs k)) ∨
      ((∀ s, stateValue M γ (Policy.ofDet (πs k)) s ≤
          stateValue M γ (Policy.ofDet (πs (k + 1))) s) ∧
        ∃ s, stateValue M γ (Policy.ofDet (πs k)) s <
          stateValue M γ (Policy.ofDet (πs (k + 1))) s)) ∧
    (∃ K : ℕ, ∀ k, K ≤ k → IsOptimalPolicy M γ (Policy.ofDet (πs k)) ∧
      ∀ s, stateValue M γ (Policy.ofDet (πs k)) s = optimalValue M γ s) := by
  have hstep : ∀ k s, stateValue M γ (Policy.ofDet (πs k)) s ≤
      stateValue M γ (Policy.ofDet (πs (k + 1))) s := fun k s =>
    P2M2d87508b.greedy_step M γ hγ0 hγ1 _ _ (hgreedy k) s
  have part1 : ∀ k, IsOptimalPolicy M γ (Policy.ofDet (πs k)) ∨
      ((∀ s, stateValue M γ (Policy.ofDet (πs k)) s ≤
          stateValue M γ (Policy.ofDet (πs (k + 1))) s) ∧
        ∃ s, stateValue M γ (Policy.ofDet (πs k)) s <
          stateValue M γ (Policy.ofDet (πs (k + 1))) s) := by
    intro k
    by_cases hs : ∃ s, stateValue M γ (Policy.ofDet (πs k)) s <
        stateValue M γ (Policy.ofDet (πs (k + 1))) s
    · exact Or.inr ⟨hstep k, hs⟩
    · left
      push Not at hs
      exact P2M2d87508b.opt_of_eq M γ hγ0 hγ1 _ _ (hgreedy k)
        (fun s => le_antisymm (hs s) (hstep k s))
  refine ⟨part1, ?_⟩
  -- monotonicity of the value sequence
  have hmono : Monotone (fun k => stateValue M γ (Policy.ofDet (πs k))) :=
    monotone_nat_of_le_succ fun k s => hstep k s
  -- some policy is optimal
  have hex : ∃ K, IsOptimalPolicy M γ (Policy.ofDet (πs K)) := by
    by_contra hno
    push Not at hno
    have hinj : Function.Injective πs := by
      intro i j hij
      by_contra hne
      have key : ∀ i j, i < j → πs i = πs j → False := by
        intro i j hlt he
        rcases part1 i with ho | ⟨-, s, hs⟩
        · exact hno i ho
        · have h1 : stateValue M γ (Policy.ofDet (πs (i + 1))) s ≤
              stateValue M γ (Policy.ofDet (πs j)) s := hmono (Nat.succ_le_of_lt hlt) s
          rw [← he] at h1
          linarith
      rcases lt_or_gt_of_ne hne with h | h
      · exact key i j h hij
      · exact key j i h hij.symm
    exact not_injective_infinite_finite πs hinj
  obtain ⟨K, hK⟩ := hex
  have hall : ∀ k, K ≤ k → IsOptimalPolicy M γ (Policy.ofDet (πs k)) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hK
    | succ n _ ih =>
      intro π' s
      exact le_trans (ih π' s) (hstep n s)
  exact ⟨K, fun k hk => ⟨hall k hk, fun s =>
    P2M2d87508b.optVal_of_opt M γ _ (hall k hk) s⟩⟩
