-- Prove2me | solution 1 for SuttonBartoRL.EpsSoft.eps_env_bellman_optimality_unique
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T18:14:15.796101+00:00
-- url     : https://prove2.me/submissions/0bb41dd5-3520-4323-ab36-04eff46bc87d

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_ValueFunctions
import Definitions.Def_SuttonBartoRL_EpsSoft_NewEnvironment

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


section OPT
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]

noncomputable def Bop (M : MDP S A) (γ : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty (fun a => Qf M γ v s a)

theorem Qf_lip (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (v w : S → ℝ) (s : S) (a : A) :
    Qf M γ v s a ≤ Qf M γ w s a + γ * dist v w := by
  rw [Qf_eq, Qf_eq]
  have h : ∑ s', M.trans s a s' * v s' ≤ ∑ s', M.trans s a s' * w s' + dist v w := by
    have hs : ∑ s', M.trans s a s' = 1 := M.p_sum s a
    calc ∑ s', M.trans s a s' * v s' ≤ ∑ s', M.trans s a s' * (w s' + dist v w) := by
          apply Finset.sum_le_sum; intro s' _
          apply mul_le_mul_of_nonneg_left _ (trans_nonneg M s a s')
          have := dist_le_pi_dist v w s'
          rw [Real.dist_eq] at this
          linarith [le_abs_self (v s' - w s')]
      _ = ∑ s', M.trans s a s' * w s' + dist v w := by
          simp_rw [mul_add]; rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]
  nlinarith

theorem Bop_le (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (v w : S → ℝ) (s : S) :
    Bop M γ v s ≤ Bop M γ w s + γ * dist v w := by
  unfold Bop
  apply Finset.sup'_le
  intro a _
  have := Finset.le_sup' (fun a => Qf M γ w s a) (Finset.mem_univ a)
  have h2 := Qf_lip M γ hγ0 v w s a
  linarith

theorem Bop_fix (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ V : S → ℝ, Bop M γ V = V ∧ ∀ w, Bop M γ w = w → w = V := by
  have hK : ((Real.toNNReal γ : NNReal) : ℝ) = γ := Real.coe_toNNReal γ hγ0
  have hc : ContractingWith (Real.toNNReal γ) (Bop M γ) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun V W => ?_⟩
    · rw [← NNReal.coe_lt_coe, hK]; simpa using hγ1
    · rw [hK, dist_pi_le_iff (by positivity)]
      intro s
      rw [Real.dist_eq, abs_le]
      have h1 := Bop_le M γ hγ0 V W s
      have h2 := Bop_le M γ hγ0 W V s
      rw [dist_comm W V] at h2
      constructor <;> linarith
  refine ⟨ContractingWith.fixedPoint (Bop M γ) hc, ContractingWith.fixedPoint_isFixedPt hc,
    fun w hw => ?_⟩
  exact hc.fixedPoint_unique hw

def detPol (d : S → A) : SuttonBartoRL.FiniteMDP.Policy S A where
  prob s a := if a = d s then 1 else 0
  nonneg s a := by split_ifs <;> norm_num
  sum_one s := by simp

theorem opt_main (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ V : S → ℝ, Bop M γ V = V ∧ (∀ s, optimalValue M γ s = V s) ∧
      ∀ w, Bop M γ w = w → w = V := by
  obtain ⟨V, hV, huniq⟩ := Bop_fix M γ hγ0 hγ1
  refine ⟨V, hV, ?_, huniq⟩
  have hex : ∀ s, ∃ a, V s = Qf M γ V s a := by
    intro s
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun a => Qf M γ V s a)
    exact ⟨a, (congrFun hV s).symm.trans ha⟩
  let d : S → A := fun s => Classical.choose (hex s)
  have hd : ∀ s, V s = Qf M γ V s (d s) := fun s => Classical.choose_spec (hex s)
  let δ : SuttonBartoRL.FiniteMDP.Policy S A := detPol d
  have hTd : ∀ v : S → ℝ, ∀ s, ∑ a, δ.prob s a * Qf M γ v s a = Qf M γ v s (d s) := by
    intro v s
    simp [δ, detPol]
  set vd := stateValue M γ δ
  have hvd : ∀ s, vd s = policyReward M δ s + γ * (policyTrans M δ).mulVec vd s :=
    fun s => bellman M γ hγ0 hγ1 δ s
  have hVd : ∀ s, V s = policyReward M δ s + γ * (policyTrans M δ).mulVec V s := by
    intro s; rw [← T_eq, hTd]; exact hd s
  have hD : dist vd V ≤ γ * dist vd V := by
    rw [dist_pi_le_iff (mul_nonneg hγ0 dist_nonneg)]
    intro s
    rw [Real.dist_eq, hvd s, hVd s]
    have e : policyReward M δ s + γ * (policyTrans M δ).mulVec vd s -
        (policyReward M δ s + γ * (policyTrans M δ).mulVec V s) =
        γ * (policyTrans M δ).mulVec (vd - V) s := by
      rw [Matrix.mulVec_sub]; simp only [Pi.sub_apply]; ring
    rw [e, abs_mul, abs_of_nonneg hγ0]
    apply mul_le_mul_of_nonneg_left _ hγ0
    apply stoch_bound (pol_stoch M δ)
    intro s'
    have := dist_le_pi_dist vd V s'
    rwa [Real.dist_eq] at this
  have hD0 : dist vd V = 0 := by
    have := dist_nonneg (x := vd) (y := V)
    nlinarith
  have hvdV : vd = V := dist_eq_zero.1 hD0
  have hQ : ∀ s a, Qf M γ V s a ≤ V s := by
    intro s a
    have := Finset.le_sup' (fun a => Qf M γ V s a) (Finset.mem_univ a)
    calc Qf M γ V s a ≤ Bop M γ V s := this
      _ = V s := congrFun hV s
  have hdom := dominate M γ hγ0 hγ1 V hQ
  intro s
  haveI : Nonempty (SuttonBartoRL.FiniteMDP.Policy S A) := ⟨δ⟩
  apply le_antisymm
  · exact ciSup_le fun σ => hdom σ s
  · calc V s = vd s := by rw [hvdV]
      _ ≤ optimalValue M γ s :=
        le_ciSup (f := fun σ => stateValue M γ σ s) ⟨V s, by rintro _ ⟨σ, rfl⟩; exact hdom σ s⟩ δ

theorem sup_aff (f : A → ℝ) (c K : ℝ) (hc : 0 ≤ c) :
    Finset.univ.sup' Finset.univ_nonempty (fun a => c * f a + K) =
      c * Finset.univ.sup' Finset.univ_nonempty f + K := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    have := Finset.le_sup' f (Finset.mem_univ a)
    nlinarith
  · obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    rw [ha]
    exact Finset.le_sup' (fun a => c * f a + K) (Finset.mem_univ a)
end OPT

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    (∀ s, optimalValue (epsEnv M ε hε0.le hε1) γ s =
        Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ s', ∑ r ∈ M.R,
          ((1 - ε) * M.p s a s' r + ∑ a', ε / (Fintype.card A : ℝ) * M.p s a' s' r) *
            (r + γ * optimalValue (epsEnv M ε hε0.le hε1) γ s'))) ∧
    (∀ s, optimalValue (epsEnv M ε hε0.le hε1) γ s =
        (1 - ε) * Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ s', ∑ r ∈ M.R,
          M.p s a s' r * (r + γ * optimalValue (epsEnv M ε hε0.le hε1) γ s')) +
        ε / (Fintype.card A : ℝ) * ∑ a, ∑ s', ∑ r ∈ M.R,
          M.p s a s' r * (r + γ * optimalValue (epsEnv M ε hε0.le hε1) γ s')) ∧
    (∀ w : S → ℝ, (∀ s, w s =
        Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ s', ∑ r ∈ M.R,
          ((1 - ε) * M.p s a s' r + ∑ a', ε / (Fintype.card A : ℝ) * M.p s a' s' r) *
            (r + γ * w s'))) →
      w = optimalValue (epsEnv M ε hε0.le hε1) γ) := by
  classical
  obtain ⟨V, hV, hopt, huniq⟩ := opt_main (epsEnv M ε hε0.le hε1) γ hγ0 hγ1
  have hOV : optimalValue (epsEnv M ε hε0.le hε1) γ = V := funext hopt
  rw [hOV]
  have p1 : ∀ s, V s = Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ s', ∑ r ∈ M.R,
          ((1 - ε) * M.p s a s' r + ∑ a', ε / (Fintype.card A : ℝ) * M.p s a' s' r) *
            (r + γ * V s')) := fun s => (congrFun hV s).symm
  refine ⟨p1, fun s => ?_, fun w hw => huniq w (funext fun s => (hw s).symm)⟩
  rw [p1 s]
  set c := ε / (Fintype.card A : ℝ)
  set Q : A → ℝ := fun a => ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * V s') with hQdef
  have hq : ∀ a, ∑ s', ∑ r ∈ M.R,
      ((1 - ε) * M.p s a s' r + ∑ a', c * M.p s a' s' r) * (r + γ * V s') =
        (1 - ε) * Q a + c * ∑ a', Q a' := by
    intro a
    have hs : ∑ a', Q a' = ∑ s', ∑ r ∈ M.R, ∑ a', M.p s a' s' r * (r + γ * V s') := by
      simp only [hQdef]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro s' _
      rw [Finset.sum_comm]
    rw [hs, hQdef]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s' _
    apply Finset.sum_congr rfl; intro r _
    rw [add_mul, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro a' _; ring
  simp_rw [hq]
  rw [sup_aff Q (1 - ε) (c * ∑ a', Q a') (by linarith)]
