-- Prove2me | solution 1 for SuttonBartoRL.NStep.error_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:04:37.499609+00:00
-- url     : https://prove2.me/submissions/1b848aa4-702d-460f-9500-a3da177e53ae

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_MDP
import Definitions.Def_SuttonBartoRL_NStep_Trajectories

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace A05cdcd4

open SuttonBartoRL.NStep

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

lemma pt_nonneg (M : MDP S A) (π : Policy S A) (s s' : S) : 0 ≤ policyTrans M π s s' := by
  unfold policyTrans MDP.trans
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (π.nonneg s a) (Finset.sum_nonneg fun r _ => M.p_nonneg _ _ _ _)

lemma pt_sum (M : MDP S A) (π : Policy S A) (s : S) : ∑ s', policyTrans M π s s' = 1 := by
  unfold policyTrans MDP.trans
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.p_sum, mul_one, π.sum_one]

lemma pt_bound (M : MDP S A) (π : Policy S A) (s : S) (f : S → ℝ) (B : ℝ)
    (hf : ∀ s', |f s'| ≤ B) : |∑ s', policyTrans M π s s' * f s'| ≤ B := by
  calc |∑ s', policyTrans M π s s' * f s'| ≤ ∑ s', |policyTrans M π s s' * f s'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', policyTrans M π s s' * B := by
        apply Finset.sum_le_sum; intro s' _
        rw [abs_mul, abs_of_nonneg (pt_nonneg M π s s')]
        exact mul_le_mul_of_nonneg_left (hf s') (pt_nonneg M π s s')
    _ = B := by rw [← Finset.sum_mul, pt_sum, one_mul]

lemma era_succ (M : MDP S A) (π : Policy S A) (k : ℕ) (s : S) :
    expectedRewardAt M π (k + 1) s =
      ∑ s', policyTrans M π s s' * expectedRewardAt M π k s' := by
  unfold expectedRewardAt
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

lemma era_bound (M : MDP S A) (π : Policy S A) (k : ℕ) (s : S) :
    |expectedRewardAt M π k s| ≤ ∑ s', |policyReward M π s'| := by
  induction k generalizing s with
  | zero =>
    simp only [expectedRewardAt, pow_zero, Matrix.one_mulVec]
    exact Finset.single_le_sum (f := fun s' => |policyReward M π s'|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  | succ k ih =>
    rw [era_succ]
    exact pt_bound M π s _ _ ih

lemma bellman (M : MDP S A) (π : Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    stateValue M γ π s = policyReward M π s +
      γ * ∑ s', policyTrans M π s s' * stateValue M γ π s' := by
  have hsum : ∀ s, Summable (fun k : ℕ => γ ^ k * expectedRewardAt M π k s) := by
    intro s
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ0 hγ1).mul_right
      (∑ s', |policyReward M π s'|)) ?_
    · intro k
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 k)]
      exact mul_le_mul_of_nonneg_left (era_bound M π k s) (pow_nonneg hγ0 k)
  unfold stateValue
  rw [(hsum s).tsum_eq_zero_add]
  congr 1
  · simp [expectedRewardAt]
  · have : ∀ k : ℕ, γ ^ (k + 1) * expectedRewardAt M π (k + 1) s =
        γ * ∑ s', policyTrans M π s s' * (γ ^ k * expectedRewardAt M π k s') := by
      intro k
      simp only [era_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => by ring
    simp_rw [this]
    rw [tsum_mul_left]
    congr 1
    rw [Summable.tsum_finsetSum]
    · refine Finset.sum_congr rfl fun s' _ => ?_
      rw [tsum_mul_left]
    · intro s' _
      exact (hsum s').mul_left _

lemma segExp_succ (M : MDP S A) (π : Policy S A) (n : ℕ) (s : S) (F : Segment M (n + 1) → ℝ) :
    segmentExpectation M π (n + 1) s F = ∑ a, ∑ s', ∑ r : M.R,
      π.prob s a * M.p s a s' r *
        segmentExpectation M π n s' (fun τ => F (Fin.cons (a, s', r) τ)) := by
  unfold segmentExpectation
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A × S × M.R)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s' _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, segmentProb, Fin.cons_zero, Fin.tail_cons]
  ring

lemma segExp_one (M : MDP S A) (π : Policy S A) (n : ℕ) (s : S) :
    segmentExpectation M π n s (fun _ => 1) = 1 := by
  induction n generalizing s with
  | zero => simp [segmentExpectation, segmentProb]
  | succ n ih =>
    rw [segExp_succ]
    simp only [ih, mul_one]
    rw [← π.sum_one s]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun s' _ => Finset.sum_coe_sort M.R (fun r => M.p s a s' r),
      M.p_sum, mul_one]

lemma segExp_affine (M : MDP S A) (π : Policy S A) (n : ℕ) (s : S) (c d : ℝ)
    (F : Segment M n → ℝ) :
    segmentExpectation M π n s (fun τ => c + d * F τ) =
      c + d * segmentExpectation M π n s F := by
  have h1 := segExp_one M π n s
  unfold segmentExpectation at *
  simp only [mul_one] at h1
  rw [Finset.mul_sum]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, h1, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => by ring

lemma states_cons (M : MDP S A) {n : ℕ} (s : S) (x : A × S × M.R) (τ : Segment M n) :
    segmentStates M s (Fin.cons x τ : Segment M (n + 1)) (Fin.last (n + 1)) =
      segmentStates M x.2.1 τ (Fin.last n) := by
  unfold segmentStates
  rw [← Fin.succ_last, Fin.cons_succ]
  have h : ∀ i : Fin (n + 1), ((Fin.cons x τ : Segment M (n + 1)) i).2.1 =
      (Fin.cons x.2.1 (fun k => (τ k).2.1) : Fin (n + 1) → S) i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i <;> simp
  exact h _

lemma ret_cons (M : MDP S A) (γ : ℝ) (V : S → ℝ) {n : ℕ} (s : S) (x : A × S × M.R)
    (τ : Segment M n) :
    nStepReturnOn M γ V s (Fin.cons x τ : Segment M (n + 1)) =
      (x.2.2 : ℝ) + γ * nStepReturnOn M γ V x.2.1 τ := by
  unfold nStepReturnOn
  rw [states_cons, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, one_mul]
  have h1 : ∑ k : Fin n, γ ^ ((k : ℕ) + 1) * ((τ k).2.2 : ℝ) =
      γ * ∑ k : Fin n, γ ^ (k : ℕ) * ((τ k).2.2 : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1]
  ring

lemma enr_zero (M : MDP S A) (π : Policy S A) (γ : ℝ) (V : S → ℝ) (s : S) :
    expectedNStepReturn M π γ V 0 s = V s := by
  simp [expectedNStepReturn, segmentExpectation, segmentProb, nStepReturnOn, segmentStates]

lemma enr_succ (M : MDP S A) (π : Policy S A) (γ : ℝ) (V : S → ℝ) (n : ℕ) (s : S) :
    expectedNStepReturn M π γ V (n + 1) s = policyReward M π s +
      γ * ∑ s', policyTrans M π s s' * expectedNStepReturn M π γ V n s' := by
  unfold expectedNStepReturn
  rw [segExp_succ]
  simp only [ret_cons, segExp_affine]
  set E := fun s' => segmentExpectation M π n s' (nStepReturnOn M γ V s') with hE
  have key : ∀ a s' (r : M.R), π.prob s a * M.p s a s' r *
      ((r : ℝ) + γ * segmentExpectation M π n s' (nStepReturnOn M γ V s')) =
      π.prob s a * ((r : ℝ) * M.p s a s' r) + γ * (π.prob s a * M.p s a s' r) * E s' := by
    intro a s' r; simp only [hE]; ring
  simp only [key, Finset.sum_add_distrib]
  congr 1
  · unfold policyReward MDP.expReward
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_coe_sort M.R (fun r => r * ∑ s', M.p s a s' r)]
  · unfold policyTrans MDP.trans
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort M.R, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring

lemma main_bound (M : MDP S A) (π : Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (V : S → ℝ) (m : ℝ) (hm : ∀ s, |V s - stateValue M γ π s| ≤ m) (n : ℕ) (s : S) :
    |expectedNStepReturn M π γ V n s - stateValue M γ π s| ≤ γ ^ n * m := by
  induction n generalizing s with
  | zero => rw [enr_zero, pow_zero, one_mul]; exact hm s
  | succ n ih =>
    have h : expectedNStepReturn M π γ V (n + 1) s - stateValue M γ π s =
        γ * ∑ s', policyTrans M π s s' *
          (expectedNStepReturn M π γ V n s' - stateValue M γ π s') := by
      rw [enr_succ, bellman M π γ hγ0 hγ1 s]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [h, abs_mul, abs_of_nonneg hγ0, pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left (pt_bound M π s _ _ ih) hγ0

end A05cdcd4

open SuttonBartoRL.NStep in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A]
    (M : MDP S A) (π : Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (V : S → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun s => |expectedNStepReturn M π γ V n s - stateValue M γ π s|) ≤
      γ ^ n * Finset.univ.sup' Finset.univ_nonempty (fun s => |V s - stateValue M γ π s|) := by
  refine Finset.sup'_le _ _ fun s _ => ?_
  exact A05cdcd4.main_bound M π γ hγ0 hγ1 V _
    (fun s' => Finset.le_sup' (fun s => |V s - stateValue M γ π s|) (Finset.mem_univ s')) n s
