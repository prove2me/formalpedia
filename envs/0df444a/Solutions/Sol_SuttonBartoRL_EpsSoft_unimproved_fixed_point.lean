-- Prove2me | solution 1 for SuttonBartoRL.EpsSoft.unimproved_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T18:11:11.585135+00:00
-- url     : https://prove2.me/submissions/df5c52f6-170b-44f1-b7c4-4787f2161624

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_EpsSoftPolicies

open SuttonBartoRL.EpsSoft Finset Filter

section GN
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

def IsStoch (Q : Matrix S S ℝ) : Prop := (∀ i j, 0 ≤ Q i j) ∧ ∀ i, ∑ j, Q i j = 1

theorem stoch_mul {P Q : Matrix S S ℝ} (hP : IsStoch P) (hQ : IsStoch Q) : IsStoch (P * Q) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]; exact Finset.sum_nonneg fun l _ => mul_nonneg (hP.1 _ _) (hQ.1 _ _)
  · simp_rw [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hQ.2, mul_one]
    exact hP.2 i

theorem stoch_one : IsStoch (1 : Matrix S S ℝ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.one_apply]; split_ifs <;> norm_num
  · simp [Matrix.one_apply]

theorem stoch_pow {P : Matrix S S ℝ} (hP : IsStoch P) : ∀ k, IsStoch (P ^ k)
  | 0 => by rw [pow_zero]; exact stoch_one
  | k + 1 => by rw [pow_succ]; exact stoch_mul (stoch_pow hP k) hP

theorem mulVec_apply' (Q : Matrix S S ℝ) (v : S → ℝ) (s : S) :
    Q.mulVec v s = ∑ s', Q s s' * v s' := rfl

theorem stoch_bound {Q : Matrix S S ℝ} (hQ : IsStoch Q) (v : S → ℝ) (B : ℝ)
    (hv : ∀ s, |v s| ≤ B) (s : S) : |Q.mulVec v s| ≤ B := by
  rw [mulVec_apply']
  calc |∑ s', Q s s' * v s'| ≤ ∑ s', |Q s s' * v s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', Q s s' * B := Finset.sum_le_sum fun s' _ => by
        rw [abs_mul, abs_of_nonneg (hQ.1 _ _)]; exact mul_le_mul_of_nonneg_left (hv s') (hQ.1 _ _)
    _ = B := by rw [← Finset.sum_mul, hQ.2, one_mul]

theorem stoch_mono {Q : Matrix S S ℝ} (hQ : IsStoch Q) {v w : S → ℝ} (h : ∀ s, v s ≤ w s)
    (s : S) : Q.mulVec v s ≤ Q.mulVec w s := by
  rw [mulVec_apply', mulVec_apply']
  exact Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h s') (hQ.1 _ _)

theorem trans_nonneg (M : MDP S A) (s : S) (a : A) (s' : S) : 0 ≤ M.trans s a s' :=
  Finset.sum_nonneg fun r _ => M.p_nonneg _ _ _ _

theorem pol_stoch (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) : IsStoch (policyTrans M π) := by
  refine ⟨fun i j => Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg _ _) (trans_nonneg M _ _ _),
    fun i => ?_⟩
  unfold policyTrans
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have : ∀ a, ∑ s', M.trans i a s' = 1 := fun a => M.p_sum i a
  simp_rw [this, mul_one]
  exact π.sum_one i

def Qf (M : MDP S A) (γ : ℝ) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s')

theorem Qf_eq (M : MDP S A) (γ : ℝ) (v : S → ℝ) (s : S) (a : A) :
    Qf M γ v s a = M.expReward s a + γ * ∑ s', M.trans s a s' * v s' := by
  unfold Qf MDP.expReward MDP.trans
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s' _; ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s' _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _; ring

theorem T_eq (M : MDP S A) (γ : ℝ) (σ : SuttonBartoRL.FiniteMDP.Policy S A) (v : S → ℝ) (s : S) :
    ∑ a, σ.prob s a * Qf M γ v s a =
      policyReward M σ s + γ * (policyTrans M σ).mulVec v s := by
  simp_rw [Qf_eq, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [mulVec_apply']
  unfold policyTrans
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro s' _; ring

theorem x_bound (M : MDP S A) (σ : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) (s : S) :
    |expectedRewardAt M σ k s| ≤ ∑ s, |policyReward M σ s| :=
  stoch_bound (stoch_pow (pol_stoch M σ) k) _ _
    (fun s => Finset.single_le_sum (f := fun s => |policyReward M σ s|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)) s

theorem x_summ (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (σ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    Summable (fun k => γ ^ k * expectedRewardAt M σ k s) := by
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ0 hγ1).mul_right
    (∑ s, |policyReward M σ s|))
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 k)]
  exact mul_le_mul_of_nonneg_left (x_bound M σ k s) (pow_nonneg hγ0 k)

theorem x_succ (M : MDP S A) (σ : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) (s : S) :
    expectedRewardAt M σ (k+1) s = ∑ s', policyTrans M σ s s' * expectedRewardAt M σ k s' := by
  unfold expectedRewardAt
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

theorem bellman (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (σ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    stateValue M γ σ s = policyReward M σ s + γ * (policyTrans M σ).mulVec (stateValue M γ σ) s := by
  rw [mulVec_apply']
  show ∑' k, γ ^ k * expectedRewardAt M σ k s = policyReward M σ s +
    γ * ∑ s', policyTrans M σ s s' * ∑' k, γ ^ k * expectedRewardAt M σ k s'
  rw [(x_summ M γ hγ0 hγ1 σ s).tsum_eq_zero_add]
  have e : ∀ k, γ ^ (k+1) * expectedRewardAt M σ (k+1) s =
      ∑ s', γ * policyTrans M σ s s' * (γ ^ k * expectedRewardAt M σ k s') := by
    intro k
    rw [x_succ, Finset.mul_sum]; apply Finset.sum_congr rfl; intro s' _; ring
  simp_rw [e]
  rw [Summable.tsum_finsetSum (fun s' _ => (x_summ M γ hγ0 hγ1 σ s').mul_left _)]
  simp_rw [tsum_mul_left]
  have h0 : γ ^ 0 * expectedRewardAt M σ 0 s = policyReward M σ s := by
    simp [expectedRewardAt]
  rw [h0, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro s' _; ring

theorem dominate (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (V : S → ℝ)
    (hQ : ∀ s a, Qf M γ V s a ≤ V s) (σ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) : stateValue M γ σ s ≤ V s := by
  set P := policyTrans M σ
  have hP := pol_stoch M σ
  have hT : ∀ s, policyReward M σ s + γ * P.mulVec V s ≤ V s := by
    intro s
    rw [← T_eq]
    calc ∑ a, σ.prob s a * Qf M γ V s a ≤ ∑ a, σ.prob s a * V s :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hQ s a) (σ.nonneg _ _)
      _ = V s := by rw [← Finset.sum_mul, σ.sum_one, one_mul]
  have hit : ∀ T s, ∑ k ∈ range T, γ ^ k * expectedRewardAt M σ k s +
      γ ^ T * (P ^ T).mulVec V s ≤ V s := by
    intro T
    induction T with
    | zero => intro s; simp
    | succ T ih =>
      intro s
      have hm := stoch_mono (stoch_pow hP T) (v := policyReward M σ + γ • P.mulVec V) (w := V)
        (fun s => by simpa using hT s) s
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ] at hm
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hm
      have := ih s
      rw [Finset.sum_range_succ]
      have hg : 0 ≤ γ ^ T := pow_nonneg hγ0 T
      have := mul_le_mul_of_nonneg_left hm hg
      unfold expectedRewardAt at *
      rw [pow_succ γ T]
      nlinarith
  have h1 := (x_summ M γ hγ0 hγ1 σ s).hasSum.tendsto_sum_nat
  set B := ∑ s, |V s|
  have hB : ∀ s, |V s| ≤ B := fun s =>
    Finset.single_le_sum (f := fun s => |V s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have h2 : Tendsto (fun T => γ ^ T * (P ^ T).mulVec V s) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun T => γ ^ T * B)
    · intro T
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 T)]
      exact mul_le_mul_of_nonneg_left (stoch_bound (stoch_pow hP T) V B hB s) (pow_nonneg hγ0 T)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const B
  have := h1.add h2
  rw [add_zero] at this
  exact le_of_tendsto' this (fun T => hit T s)

theorem dominated (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (V : S → ℝ)
    (σ : SuttonBartoRL.FiniteMDP.Policy S A) (hT : ∀ s, V s ≤ policyReward M σ s + γ * (policyTrans M σ).mulVec V s)
    (s : S) : V s ≤ stateValue M γ σ s := by
  set P := policyTrans M σ
  have hP := pol_stoch M σ
  have hit : ∀ T s, V s ≤ ∑ k ∈ range T, γ ^ k * expectedRewardAt M σ k s +
      γ ^ T * (P ^ T).mulVec V s := by
    intro T
    induction T with
    | zero => intro s; simp
    | succ T ih =>
      intro s
      have hm := stoch_mono (stoch_pow hP T) (w := policyReward M σ + γ • P.mulVec V) (v := V)
        (fun s => by simpa using hT s) s
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ] at hm
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hm
      have := ih s
      rw [Finset.sum_range_succ]
      have hg : 0 ≤ γ ^ T := pow_nonneg hγ0 T
      have := mul_le_mul_of_nonneg_left hm hg
      unfold expectedRewardAt at *
      rw [pow_succ γ T]
      nlinarith
  have h1 := (x_summ M γ hγ0 hγ1 σ s).hasSum.tendsto_sum_nat
  set B := ∑ s, |V s|
  have hB : ∀ s, |V s| ≤ B := fun s =>
    Finset.single_le_sum (f := fun s => |V s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have h2 : Tendsto (fun T => γ ^ T * (P ^ T).mulVec V s) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun T => γ ^ T * B)
    · intro T
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 T)]
      exact mul_le_mul_of_nonneg_left (stoch_bound (stoch_pow hP T) V B hB s) (pow_nonneg hγ0 T)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const B
  have := h1.add h2
  rw [add_zero] at this
  exact ge_of_tendsto' this (fun T => hit T s)
end GN

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (π π' : SuttonBartoRL.FiniteMDP.Policy S A) (hπ : IsEpsSoft ε π)
    (hπ' : IsEpsGreedy M γ ε π π') (heq : ∀ s, stateValue M γ π' s = stateValue M γ π s) :
    ∀ s, (stateValue M γ π s =
        (1 - ε) * Finset.univ.sup' Finset.univ_nonempty (fun a => actionValue M γ π s a) +
          ε / (Fintype.card A : ℝ) * ∑ a, actionValue M γ π s a) ∧
      stateValue M γ π s =
        (1 - ε) * Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ s', ∑ r ∈ M.R,
          M.p s a s' r * (r + γ * stateValue M γ π s')) +
        ε / (Fintype.card A : ℝ) * ∑ a, ∑ s', ∑ r ∈ M.R,
          M.p s a s' r * (r + γ * stateValue M γ π s') := by
  obtain ⟨g, hg, hp⟩ := hπ'
  have hVU : stateValue M γ π' = stateValue M γ π := funext heq
  have key : ∀ s, stateValue M γ π s = ∑ a, π'.prob s a * actionValue M γ π s a := by
    intro s
    rw [← heq s, bellman M γ hγ0 hγ1 π' s, ← T_eq]
    unfold actionValue Qf
    rw [hVU]
  have hsup : ∀ s, Finset.univ.sup' Finset.univ_nonempty (fun a => actionValue M γ π s a) =
      actionValue M γ π s (g s) := by
    intro s
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun a _ => hg s a
    · exact Finset.le_sup' (fun a => actionValue M γ π s a) (Finset.mem_univ (g s))
  have main : ∀ s, stateValue M γ π s =
      (1 - ε) * Finset.univ.sup' Finset.univ_nonempty (fun a => actionValue M γ π s a) +
        ε / (Fintype.card A : ℝ) * ∑ a, actionValue M γ π s a := by
    intro s
    rw [key s, hsup s]
    have e : ∀ a, π'.prob s a * actionValue M γ π s a = ε / (Fintype.card A : ℝ) * actionValue M γ π s a +
        (if a = g s then (1 - ε) * actionValue M γ π s a else 0) := by
      intro a
      rw [hp s a]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring
  intro s
  exact ⟨main s, main s⟩
