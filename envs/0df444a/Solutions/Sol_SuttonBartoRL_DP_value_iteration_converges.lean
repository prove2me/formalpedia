-- Prove2me | solution 1 for SuttonBartoRL.DP.value_iteration_converges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:28:17.708765+00:00
-- url     : https://prove2.me/submissions/ff84427b-bc90-4b1c-b922-d72980324c9f

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P2Mcab01c66

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

lemma vIU_eq [Nonempty A] (M : MDP S A) (γ : ℝ) : valueIterUpdate M γ = Tm M γ := rfl

lemma Tm_le [Nonempty A] (M : MDP S A) (γ : ℝ) (h0 : 0 ≤ γ) (u w : S → ℝ) (c : ℝ)
    (h : ∀ t, u t ≤ w t + c) (s : S) : Tm M γ u s ≤ Tm M γ w s + γ * c := by
  unfold Tm
  refine Finset.sup'_le _ _ fun a _ => ?_
  have h1 := Q_mono M γ h0 u (fun t => w t + c) h s a
  rw [Q_add_const] at h1
  have h2 : Q M γ w s a ≤ Finset.univ.sup' Finset.univ_nonempty (fun a => Q M γ w s a) :=
    Finset.le_sup' (fun a => Q M γ w s a) (Finset.mem_univ a)
  linarith

lemma Tm_dist [Nonempty A] (M : MDP S A) (γ : ℝ) (h0 : 0 ≤ γ) (u w : S → ℝ) :
    dist (Tm M γ u) (Tm M γ w) ≤ γ * dist u w := by
  have hd : ∀ t, |u t - w t| ≤ dist u w := by
    intro t
    have := dist_le_pi_dist u w t
    rwa [Real.dist_eq] at this
  refine (dist_pi_le_iff (mul_nonneg h0 dist_nonneg)).2 fun s => ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor
  · have := Tm_le M γ h0 u w (dist u w) (fun t => by linarith [(abs_sub_le_iff.1 (hd t)).1]) s
    linarith
  · have := Tm_le M γ h0 w u (dist u w) (fun t => by linarith [(abs_sub_le_iff.1 (hd t)).2]) s
    linarith

lemma contracting [Nonempty A] (M : MDP S A) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1) :
    ContractingWith (Real.toNNReal γ) (valueIterUpdate M γ) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun u w => ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ h0, NNReal.coe_one]
    exact h1
  · rw [vIU_eq, Real.coe_toNNReal _ h0]
    exact Tm_dist M γ h0 u w

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

lemma value_ge [Nonempty A] [DecidableEq A] (M : MDP S A) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1)
    (v : S → ℝ) (d : S → A) (hd : ∀ s, v s ≤ Q M γ v s (d s)) (s : S) :
    v s ≤ stateValue M γ (Policy.ofDet d) s := by
  set w := stateValue M γ (Policy.ofDet d) with hw
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
  have h2 := Q_mono M γ h0 _ _ hle x (d x)
  rw [Q_add_const] at h2
  have h3 : w x = Q M γ w x (d x) := bellman_det M d γ h0 h1 x
  have h4 : γ * m < m := mul_lt_of_lt_one_left hmpos h1
  have h5 := hd x
  linarith

lemma main [Nonempty A] (M : MDP S A) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1) (v : S → ℝ)
    (hfix : ∀ s, Tm M γ v s = v s) :
    (∃ π : Policy S A, ∀ s, stateValue M γ π s = optimalValue M γ s) ∧
      optimalValue M γ = v := by
  classical
  have hex : ∀ s, ∃ a, Tm M γ v s = Q M γ v s a := by
    intro s
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := A))
      (fun a => Q M γ v s a)
    exact ⟨a, ha⟩
  choose d hdd using hex
  have hd : ∀ s, v s ≤ Q M γ v s (d s) := fun s => by rw [← hdd, hfix]
  have heq : ∀ s, stateValue M γ (Policy.ofDet d) s = v s := fun s =>
    le_antisymm (value_le M γ h0 h1 v hfix _ s) (value_ge M γ h0 h1 v d hd s)
  have hopt : ∀ s, optimalValue M γ s = v s := by
    intro s
    have : Nonempty (Policy S A) := ⟨Policy.ofDet d⟩
    unfold optimalValue
    refine le_antisymm (ciSup_le fun π => value_le M γ h0 h1 v hfix π s) ?_
    have hb : BddAbove (Set.range fun π : Policy S A => stateValue M γ π s) := by
      refine ⟨v s, ?_⟩
      rintro _ ⟨π, rfl⟩
      exact value_le M γ h0 h1 v hfix π s
    rw [← heq s]
    exact le_ciSup hb (Policy.ofDet d)
  exact ⟨⟨Policy.ofDet d, fun s => by rw [heq, hopt]⟩, funext hopt⟩

end P2Mcab01c66

open SuttonBartoRL.DP in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (v₀ : S → ℝ) :
    (∃ π : Policy S A, ∀ s, stateValue M γ π s = optimalValue M γ s) ∧
    Filter.Tendsto (fun k : ℕ => (valueIterUpdate M γ)^[k] v₀) Filter.atTop
      (nhds (optimalValue M γ)) := by
  have hc := P2Mcab01c66.contracting M γ hγ0 hγ1
  have hfp := ContractingWith.fixedPoint_isFixedPt (f := valueIterUpdate M γ) hc
  have hfix : ∀ s, P2Mcab01c66.Tm M γ (ContractingWith.fixedPoint _ hc) s =
      ContractingWith.fixedPoint _ hc s := fun s => congrFun hfp s
  obtain ⟨hex, hopt⟩ := P2Mcab01c66.main M γ hγ0 hγ1 _ hfix
  refine ⟨hex, ?_⟩
  rw [hopt]
  exact hc.tendsto_iterate_fixedPoint v₀
