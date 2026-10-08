-- Prove2me | solution 1 for SuttonBartoRL.AverageReward.futility_of_discounting
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:12:25.028283+00:00
-- url     : https://prove2.me/submissions/c12c95e2-e96d-463a-87eb-d5908817496e

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

set_option autoImplicit false

namespace FutilityHelpers

open SuttonBartoRL.AverageReward

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

theorem policyTrans_nonneg (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s s' : S) :
    0 ≤ M.policyTrans π s s' := by
  unfold MDP.policyTrans MDP.trans
  exact Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg s a)
    (Finset.sum_nonneg fun r _ => M.p_nonneg s a s' r)

theorem policyTrans_rowsum (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) :
    ∑ s', M.policyTrans π s s' = 1 := by
  unfold MDP.policyTrans
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have h : ∀ a, ∑ s', M.trans s a s' = 1 := fun a => by
    unfold MDP.trans; exact M.p_sum s a
  simp [h, π.sum_one s]

theorem bound (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) (s : S) :
    |M.expectedRewardAt π k s| ≤ ∑ s', |M.policyReward π s'| := by
  unfold MDP.expectedRewardAt
  induction k generalizing s with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    exact Finset.single_le_sum (f := fun s' => |M.policyReward π s'|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    set v := Matrix.mulVec (M.policyTrans π ^ k) (M.policyReward π)
    set B := ∑ s', |M.policyReward π s'|
    show |∑ s', M.policyTrans π s s' * v s'| ≤ B
    calc |∑ s', M.policyTrans π s s' * v s'| ≤ ∑ s', |M.policyTrans π s s' * v s'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s', M.policyTrans π s s' * |v s'| := by
          congr 1; ext s'; rw [abs_mul, abs_of_nonneg (policyTrans_nonneg M π s s')]
      _ ≤ ∑ s', M.policyTrans π s s' * B := by
          gcongr with s' _
          · exact policyTrans_nonneg M π s s'
          · exact ih s'
      _ = B := by rw [← Finset.sum_mul, policyTrans_rowsum, one_mul]

theorem stat_pow (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ)
    (h : IsStationaryDist M π μ) (k : ℕ) :
    Matrix.vecMul μ (M.policyTrans π ^ k) = μ := by
  have h1 : Matrix.vecMul μ (M.policyTrans π) = μ := by
    ext s'
    exact h.2.2 s'
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, h1]

theorem avg_eq (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) :
    avgReward M π μ = ∑ s, μ s * M.policyReward π s := by
  unfold avgReward MDP.policyReward MDP.expReward
  congr 1; ext s; congr 1; congr 1; ext a; congr 1
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s' _ => ?_
  ring

theorem step_eq (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ)
    (h : IsStationaryDist M π μ) (k : ℕ) :
    ∑ s, μ s * M.expectedRewardAt π k s = avgReward M π μ := by
  rw [avg_eq]
  unfold MDP.expectedRewardAt
  have := Matrix.dotProduct_mulVec μ (M.policyTrans π ^ k) (M.policyReward π)
  rw [stat_pow M π μ h k] at this
  simpa [dotProduct] using this

theorem main (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (h : IsStationaryDist M π μ) :
    discountedObjective M γ π μ = (1 / (1 - γ)) * avgReward M π μ := by
  have hs : ∀ s, Summable (fun k : ℕ => γ ^ k * M.expectedRewardAt π k s) := by
    intro s
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |M.policyReward π s'|)) ?_
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 k)]
    exact mul_le_mul_of_nonneg_left (bound M π k s) (pow_nonneg hγ0 k)
  unfold discountedObjective MDP.stateValue
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun s _ => (hs s).mul_left (μ s))]
  have : ∀ k : ℕ, ∑ s, μ s * (γ ^ k * M.expectedRewardAt π k s) = γ ^ k * avgReward M π μ := by
    intro k
    rw [← step_eq M π μ h k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  simp_rw [this]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1]
  ring

end FutilityHelpers

open SuttonBartoRL.AverageReward in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (∀ (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ), IsStationaryDist M π μ →
      discountedObjective M γ π μ = (1 / (1 - γ)) * avgReward M π μ) ∧
    (∀ (π π' : SuttonBartoRL.FiniteMDP.Policy S A) (μ μ' : S → ℝ), IsStationaryDist M π μ → IsStationaryDist M π' μ' →
      (discountedObjective M γ π μ ≤ discountedObjective M γ π' μ' ↔
        avgReward M π μ ≤ avgReward M π' μ')) := by
  refine ⟨fun π μ h => FutilityHelpers.main M γ hγ0 hγ1 π μ h, ?_⟩
  intro π π' μ μ' h h'
  rw [FutilityHelpers.main M γ hγ0 hγ1 π μ h, FutilityHelpers.main M γ hγ0 hγ1 π' μ' h']
  have hpos : 0 < 1 / (1 - γ) := by
    apply div_pos one_pos; linarith
  exact mul_le_mul_iff_right₀ hpos
