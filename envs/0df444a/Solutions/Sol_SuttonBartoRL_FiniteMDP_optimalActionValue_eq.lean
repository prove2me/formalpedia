-- Prove2me | solution 1 for SuttonBartoRL.FiniteMDP.optimalActionValue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:54:10.09718+00:00
-- url     : https://prove2.me/submissions/5a236262-966a-4bc5-994b-71278cb18519

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

set_option autoImplicit false


open SuttonBartoRL.FiniteMDP in
theorem p64_trans_nonneg {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (s : S) (a : A) (s' : S) : 0 ≤ M.trans s a s' :=
  Finset.sum_nonneg fun r _ => M.p_nonneg s a s' r

open SuttonBartoRL.FiniteMDP in
theorem p64_trans_sum {S A : Type} [Fintype S] [Fintype A]
    (M : MDP S A) (s : S) (a : A) : ∑ s', M.trans s a s' = 1 :=
  M.p_sum s a

open SuttonBartoRL.FiniteMDP in
theorem p64_bound {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
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
      Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg s a) (p64_trans_nonneg M s a s')
    have hPs : ∑ s', policyTrans M π s s' = 1 := by
      simp only [policyTrans]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, p64_trans_sum, mul_one]
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
theorem p64_summable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) :
    Summable (fun k : ℕ => γ ^ k * expectedRewardAt M π k s) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ t, |policyReward M π t|)) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 k)]
  exact mul_le_mul_of_nonneg_left (p64_bound M π k s) (pow_nonneg hγ0 k)

open SuttonBartoRL.FiniteMDP in
theorem p64_term {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (π : Policy S A) (s : S) (a : A) (k : ℕ) :
    γ ^ (k + 1) * actionExpectedRewardAt M π s a (k + 1)
      = ∑ s', γ * M.trans s a s' * (γ ^ k * expectedRewardAt M π k s') := by
  rw [actionExpectedRewardAt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  ring

open SuttonBartoRL.FiniteMDP in
theorem p64_step {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) (a : A) :
    actionValue M γ π s a = M.expReward s a + ∑ s', γ * M.trans s a s' * stateValue M γ π s' := by
  have hs : ∀ s' ∈ (Finset.univ : Finset S),
      Summable (fun k : ℕ => γ * M.trans s a s' * (γ ^ k * expectedRewardAt M π k s')) :=
    fun s' _ => (p64_summable M γ hγ0 hγ1 π s').mul_left _
  have hsum : Summable (fun k : ℕ => γ ^ (k + 1) * actionExpectedRewardAt M π s a (k + 1)) :=
    (summable_sum hs).congr fun k => (p64_term M γ π s a k).symm
  have h1 : actionValue M γ π s a = γ ^ 0 * actionExpectedRewardAt M π s a 0
      + ∑' k : ℕ, γ ^ (k + 1) * actionExpectedRewardAt M π s a (k + 1) :=
    tsum_eq_zero_add' hsum
  rw [h1, tsum_congr (p64_term M γ π s a), Summable.tsum_finsetSum hs]
  rw [pow_zero, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun s' _ => tsum_mul_left

open SuttonBartoRL.FiniteMDP in
theorem p64_actsummable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) (a : A) :
    Summable (fun k : ℕ => γ ^ k * actionExpectedRewardAt M π s a k) := by
  have hs : ∀ s' ∈ (Finset.univ : Finset S),
      Summable (fun k : ℕ => γ * M.trans s a s' * (γ ^ k * expectedRewardAt M π k s')) :=
    fun s' _ => (p64_summable M γ hγ0 hγ1 π s').mul_left _
  have hsum : Summable (fun k : ℕ => γ ^ (k + 1) * actionExpectedRewardAt M π s a (k + 1)) :=
    (summable_sum hs).congr fun k => (p64_term M γ π s a k).symm
  exact (summable_nat_add_iff 1).mp hsum

open SuttonBartoRL.FiniteMDP in
theorem p64_termwise {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : Policy S A) (s : S) (k : ℕ) :
    ∑ a, π.prob s a * actionExpectedRewardAt M π s a k = expectedRewardAt M π k s := by
  cases k with
  | zero =>
    simp only [actionExpectedRewardAt, expectedRewardAt, pow_zero, Matrix.one_mulVec]
    rfl
  | succ k =>
    have hstep : expectedRewardAt M π (k + 1) s
        = ∑ s', policyTrans M π s s' * expectedRewardAt M π k s' := by
      simp only [expectedRewardAt]
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      rfl
    rw [hstep]
    simp only [actionExpectedRewardAt, policyTrans, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun a _ => ?_
    ring

open SuttonBartoRL.FiniteMDP in
theorem p64_vQ {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) :
    stateValue M γ π s = ∑ a, π.prob s a * actionValue M γ π s a := by
  have hs : ∀ a ∈ (Finset.univ : Finset A),
      Summable (fun k : ℕ => π.prob s a * (γ ^ k * actionExpectedRewardAt M π s a k)) :=
    fun a _ => (p64_actsummable M γ hγ0 hγ1 π s a).mul_left _
  have h1 : ∑ a, π.prob s a * actionValue M γ π s a
      = ∑ a, ∑' k : ℕ, π.prob s a * (γ ^ k * actionExpectedRewardAt M π s a k) :=
    Finset.sum_congr rfl fun a _ => tsum_mul_left.symm
  rw [h1, ← Summable.tsum_finsetSum hs, stateValue]
  refine tsum_congr fun k => ?_
  rw [← p64_termwise M π s k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

namespace P2M64e7

open SuttonBartoRL.FiniteMDP

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- One-step lookahead value of action `a` in `s` against `v`. -/
noncomputable def Q (M : MDP S A) (γ : ℝ) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  M.expReward s a + ∑ s', γ * M.trans s a s' * v s'

lemma Q_sub (M : MDP S A) (γ : ℝ) (u w : S → ℝ) (s : S) (a : A) :
    Q M γ u s a - Q M γ w s a = γ * ∑ s', M.trans s a s' * (u s' - w s') := by
  unfold Q
  rw [Finset.mul_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

lemma Q_mono (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (u w : S → ℝ) (h : ∀ s, u s ≤ w s)
    (s : S) (a : A) : Q M γ u s a ≤ Q M γ w s a := by
  have := Q_sub M γ w u s a
  have hn : 0 ≤ γ * ∑ s', M.trans s a s' * (w s' - u s') :=
    mul_nonneg hγ0 (Finset.sum_nonneg fun t _ =>
      mul_nonneg (p64_trans_nonneg M s a t) (sub_nonneg.mpr (h t)))
  linarith

lemma Q_dist (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (u w : S → ℝ) (s : S) (a : A) :
    |Q M γ u s a - Q M γ w s a| ≤ γ * dist u w := by
  rw [Q_sub, abs_mul, abs_of_nonneg hγ0]
  refine mul_le_mul_of_nonneg_left ?_ hγ0
  calc |∑ s', M.trans s a s' * (u s' - w s')|
      ≤ ∑ s', |M.trans s a s' * (u s' - w s')| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', M.trans s a s' * dist u w := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [abs_mul, abs_of_nonneg (p64_trans_nonneg M s a t)]
        refine mul_le_mul_of_nonneg_left ?_ (p64_trans_nonneg M s a t)
        have := dist_le_pi_dist u w t
        rwa [Real.dist_eq] at this
    _ = dist u w := by rw [← Finset.sum_mul, p64_trans_sum, one_mul]

variable [Nonempty A]

/-- The Bellman optimality operator. -/
noncomputable def T (M : MDP S A) (γ : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty (fun a => Q M γ v s a)

lemma T_le (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (u w : S → ℝ) (s : S) :
    T M γ u s ≤ T M γ w s + γ * dist u w := by
  unfold T
  refine Finset.sup'_le _ _ fun a _ => ?_
  have h1 := Q_dist M γ hγ0 u w s a
  have h2 : Q M γ w s a ≤ Finset.univ.sup' Finset.univ_nonempty (fun a => Q M γ w s a) :=
    Finset.le_sup' (fun a => Q M γ w s a) (Finset.mem_univ a)
  have h3 := (abs_le.mp h1).2
  linarith

lemma T_contr (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ContractingWith (⟨γ, hγ0⟩ : NNReal) (T M γ) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun u w => ?_⟩
  · have h : ((⟨γ, hγ0⟩ : NNReal) : ℝ) < ((1 : NNReal) : ℝ) := by simpa using hγ1
    exact_mod_cast h
  · show dist (T M γ u) (T M γ w) ≤ γ * dist u w
    rw [dist_pi_le_iff (mul_nonneg hγ0 dist_nonneg)]
    intro s
    rw [Real.dist_eq, abs_le]
    have h1 := T_le M γ hγ0 u w s
    have h2 := T_le M γ hγ0 w u s
    rw [dist_comm w u] at h2
    constructor <;> linarith

omit [Nonempty A] in
/-- Comparison principle: `u - w ≤ γ P_π (u - w)` forces `u ≤ w`. -/
lemma cmp (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (u w : S → ℝ)
    (h : ∀ s, u s - w s ≤ ∑ a, π.prob s a * (γ * ∑ s', M.trans s a s' * (u s' - w s'))) :
    ∀ s, u s ≤ w s := by
  intro s
  obtain ⟨s0, -, hs0⟩ := Finset.exists_max_image Finset.univ (fun t => u t - w t)
    ⟨s, Finset.mem_univ s⟩
  set d := u s0 - w s0 with hd
  have key : d ≤ γ * d := by
    calc d ≤ ∑ a, π.prob s0 a * (γ * ∑ s', M.trans s0 a s' * (u s' - w s')) := h s0
      _ ≤ ∑ a, π.prob s0 a * (γ * ∑ s', M.trans s0 a s' * d) := by
          refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (π.nonneg s0 a)
          refine mul_le_mul_of_nonneg_left ?_ hγ0
          exact Finset.sum_le_sum fun t _ =>
            mul_le_mul_of_nonneg_left (hs0 t (Finset.mem_univ t)) (p64_trans_nonneg M s0 a t)
      _ = γ * d := by
          simp_rw [← Finset.sum_mul, p64_trans_sum, one_mul]
          rw [← Finset.sum_mul, π.sum_one, one_mul]
  have hd0 : d ≤ 0 := by nlinarith
  have := hs0 s (Finset.mem_univ s)
  linarith

omit [Nonempty A] in
lemma sum_Q_sub (M : MDP S A) (γ : ℝ) (π : Policy S A) (u w : S → ℝ) (s : S) :
    ∑ a, π.prob s a * Q M γ u s a - ∑ a, π.prob s a * Q M γ w s a =
      ∑ a, π.prob s a * (γ * ∑ s', M.trans s a s' * (u s' - w s')) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Q_sub, mul_sub]

omit [Nonempty A] in
lemma vQ' (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) :
    stateValue M γ π s = ∑ a, π.prob s a * Q M γ (stateValue M γ π) s a := by
  rw [p64_vQ M γ hγ0 hγ1 π s]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [p64_step M γ hγ0 hγ1 π s a]
  rfl

omit [Nonempty A] in
lemma qQ (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) (a : A) :
    actionValue M γ π s a = Q M γ (stateValue M γ π) s a :=
  p64_step M γ hγ0 hγ1 π s a

/-- Main structure: a fixed point `v` of `T` with a greedy policy attaining it. -/
lemma main (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ v : S → ℝ, ∃ πs : Policy S A, (∀ s, stateValue M γ πs s = v s) ∧
      ∀ (π : Policy S A) s, stateValue M γ π s ≤ v s := by
  classical
  have hC := T_contr M γ hγ0 hγ1
  set v := ContractingWith.fixedPoint (T M γ) hC with hvdef
  have hv : T M γ v = v := ContractingWith.fixedPoint_isFixedPt hC
  have hTv : ∀ s, T M γ v s = v s := fun s => congrFun hv s
  choose g _ hg using fun s => Finset.exists_max_image Finset.univ (fun a => Q M γ v s a)
    (Finset.univ_nonempty (α := A))
  have hTg : ∀ s, T M γ v s = Q M γ v s (g s) := by
    intro s
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun a _ => hg s a (Finset.mem_univ a)
    · exact Finset.le_sup' (fun a => Q M γ v s a) (Finset.mem_univ (g s))
  have hQT : ∀ s a, Q M γ v s a ≤ v s := by
    intro s a
    rw [← hTv s]
    exact Finset.le_sup' (fun a => Q M γ v s a) (Finset.mem_univ a)
  let πs : Policy S A :=
    { prob := fun s a => if a = g s then 1 else 0
      nonneg := fun s a => by split_ifs <;> norm_num
      sum_one := fun s => by simp }
  have hπs : ∀ (u : S → ℝ) s, ∑ a, πs.prob s a * Q M γ u s a = Q M γ u s (g s) := by
    intro u s
    simp [πs]
  have hvπs : ∀ s, v s = ∑ a, πs.prob s a * Q M γ v s a := by
    intro s
    rw [hπs, ← hTg, hTv]
  refine ⟨v, πs, fun s => le_antisymm ?_ ?_, fun π s => ?_⟩
  · refine cmp M γ hγ0 hγ1 πs _ _ (fun t => ?_) s
    rw [vQ' M γ hγ0 hγ1 πs t, hvπs t, sum_Q_sub]
  · refine cmp M γ hγ0 hγ1 πs _ _ (fun t => ?_) s
    rw [vQ' M γ hγ0 hγ1 πs t, hvπs t, sum_Q_sub]
  · refine cmp M γ hγ0 hγ1 π _ _ (fun t => ?_) s
    have hle : ∑ a, π.prob t a * Q M γ v t a ≤ v t := by
      calc ∑ a, π.prob t a * Q M γ v t a ≤ ∑ a, π.prob t a * v t :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hQT t a) (π.nonneg t a)
        _ = v t := by rw [← Finset.sum_mul, π.sum_one, one_mul]
    have := sum_Q_sub M γ π (stateValue M γ π) v t
    rw [← vQ' M γ hγ0 hγ1 π t] at this
    linarith

end P2M64e7

open SuttonBartoRL.FiniteMDP in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    IsGreatest (Set.range fun π : Policy S A => actionValue M γ π s a)
        (optimalActionValue M γ s a) ∧
      optimalActionValue M γ s a =
        ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * optimalValue M γ s') := by
  obtain ⟨v, πs, hπs, hle⟩ := P2M64e7.main M γ hγ0 hγ1
  have : Nonempty (Policy S A) := ⟨πs⟩
  have hopt : ∀ t, optimalValue M γ t = v t := by
    intro t
    unfold optimalValue
    apply le_antisymm
    · exact ciSup_le fun π => hle π t
    · rw [← hπs t]
      exact le_ciSup (f := fun π : Policy S A => stateValue M γ π t)
        ⟨v t, by rintro _ ⟨π, rfl⟩; exact hle π t⟩ πs
  have hgr : IsGreatest (Set.range fun π : Policy S A => actionValue M γ π s a)
      (P2M64e7.Q M γ v s a) := by
    refine ⟨⟨πs, ?_⟩, ?_⟩
    · show actionValue M γ πs s a = _
      rw [P2M64e7.qQ M γ hγ0 hγ1]
      congr 1
      funext t
      exact hπs t
    · rintro _ ⟨π, rfl⟩
      show actionValue M γ π s a ≤ _
      rw [P2M64e7.qQ M γ hγ0 hγ1]
      exact P2M64e7.Q_mono M γ hγ0 _ _ (hle π) s a
  have hq : optimalActionValue M γ s a = P2M64e7.Q M γ v s a := by
    unfold optimalActionValue
    exact hgr.csSup_eq
  refine ⟨hq ▸ hgr, ?_⟩
  rw [hq]
  simp_rw [hopt]
  unfold P2M64e7.Q MDP.expReward MDP.trans
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
