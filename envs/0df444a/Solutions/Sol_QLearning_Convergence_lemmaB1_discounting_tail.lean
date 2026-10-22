-- Prove2me | solution 1 for QLearning.Convergence.lemmaB1_discounting_tail
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:39:21.224463+00:00
-- url     : https://prove2.me/submissions/b4350a21-f947-4d91-ae50-aa78db3ae90c

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open QLearning.Convergence

lemma jj_stoch {X : Type} [Fintype X] (p w : X → ℝ) (hp : ∀ y, 0 ≤ p y) (hs : ∑ y, p y = 1)
    (B : ℝ) (hw : ∀ y, |w y| ≤ B) : |∑ y, p y * w y| ≤ B := by
  calc |∑ y, p y * w y| ≤ ∑ y, |p y * w y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, p y * |w y| := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (hp y)]
    _ ≤ ∑ y, p y * B := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hw y) (hp y)
    _ = B := by rw [← Finset.sum_mul, hs, one_mul]

theorem solution {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Rbar : ℝ) (hR : ∀ x a, |M.R x a| ≤ Rbar)
    (π : X → A) (x : X) (bs : List A) :
    |seqThenPolicy M γ π x bs - seqValue M γ x bs| ≤ γ ^ bs.length * (Rbar / (1 - γ)) := by
  have hpow : ∀ t : ℕ, ∀ x : X,
      |((policyMatrix M π) ^ t).mulVec (fun z => M.R z (π z)) x| ≤ Rbar := by
    intro t
    induction t with
    | zero => intro x; simpa using hR x (π x)
    | succ t ih =>
      intro x
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, policyMatrix]
      exact jj_stoch (fun y => M.P x (π x) y) _ (fun y => M.P_nonneg _ _ _) (M.P_sum _ _) Rbar ih
  have hpv : ∀ y, |policyValue M γ π y - 0| ≤ Rbar / (1 - γ) := by
    intro y
    rw [sub_zero]
    unfold policyValue
    rw [← Real.norm_eq_abs]
    have hg : HasSum (fun t : ℕ => γ ^ t * Rbar) (Rbar / (1 - γ)) := by
      have := (hasSum_geometric_of_lt_one hγ0.le hγ1).mul_right Rbar
      rwa [← div_eq_inv_mul] at this
    refine tsum_of_norm_bounded hg (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0.le t)]
    exact mul_le_mul_of_nonneg_left (hpow t y) (pow_nonneg hγ0.le t)
  have key : ∀ (V W : X → ℝ) (c : ℝ), (∀ y, |V y - W y| ≤ c) → ∀ (bs : List A) (x : X),
      |seqValueWith M γ V x bs - seqValueWith M γ W x bs| ≤ γ ^ bs.length * c := by
    intro V W c hc bs
    induction bs with
    | nil => intro x; simpa [seqValueWith] using hc x
    | cons b bs ih =>
      intro x
      simp only [seqValueWith, List.length_cons]
      have e : (M.R x b + γ * ∑ y, M.P x b y * seqValueWith M γ V y bs) -
          (M.R x b + γ * ∑ y, M.P x b y * seqValueWith M γ W y bs) =
          γ * ∑ y, M.P x b y * (seqValueWith M γ V y bs - seqValueWith M γ W y bs) := by
        simp only [mul_sub, Finset.sum_sub_distrib]; ring
      rw [e, abs_mul, abs_of_pos hγ0]
      have := jj_stoch (fun y => M.P x b y)
        (fun y => seqValueWith M γ V y bs - seqValueWith M γ W y bs)
        (fun y => M.P_nonneg _ _ _) (M.P_sum _ _) (γ ^ bs.length * c) (fun y => ih y)
      calc γ * |∑ y, M.P x b y * (seqValueWith M γ V y bs - seqValueWith M γ W y bs)|
          ≤ γ * (γ ^ bs.length * c) := mul_le_mul_of_nonneg_left this hγ0.le
        _ = γ ^ (bs.length + 1) * c := by ring
  exact key (policyValue M γ π) (fun _ => 0) _ hpv bs x
