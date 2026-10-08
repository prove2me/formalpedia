-- Prove2me | solution 1 for SuttonBartoRL.DP.iterative_policy_evaluation_converges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:55:52.55768+00:00
-- url     : https://prove2.me/submissions/a326603d-96a1-4de7-adf2-17d5bf0ef29e

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

set_option autoImplicit false

namespace SuttonBartoRL.DP.IPEAux

open SuttonBartoRL.DP Matrix

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

lemma policyTrans_nonneg (M : MDP S A) (π : Policy S A) (s s' : S) :
    0 ≤ policyTrans M π s s' := by
  unfold policyTrans MDP.trans
  exact Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg s a)
    (Finset.sum_nonneg fun r _ => M.p_nonneg s a s' r)

lemma policyTrans_rowsum (M : MDP S A) (π : Policy S A) (s : S) :
    ∑ s', policyTrans M π s s' = 1 := by
  unfold policyTrans MDP.trans
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.p_sum, mul_one]
  exact π.sum_one s

lemma mulVec_bound (M : MDP S A) (π : Policy S A) (x : S → ℝ) (B : ℝ)
    (hx : ∀ s, |x s| ≤ B) (s : S) : |(policyTrans M π *ᵥ x) s| ≤ B := by
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ s', policyTrans M π s s' * x s'|
      ≤ ∑ s', |policyTrans M π s s' * x s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', policyTrans M π s s' * B := by
        refine Finset.sum_le_sum fun s' _ => ?_
        rw [abs_mul, abs_of_nonneg (policyTrans_nonneg M π s s')]
        exact mul_le_mul_of_nonneg_left (hx s') (policyTrans_nonneg M π s s')
    _ = B := by rw [← Finset.sum_mul, policyTrans_rowsum, one_mul]

lemma pow_mulVec_bound (M : MDP S A) (π : Policy S A) (x : S → ℝ) (B : ℝ)
    (hx : ∀ s, |x s| ≤ B) (k : ℕ) (s : S) : |(policyTrans M π ^ k *ᵥ x) s| ≤ B := by
  induction k generalizing s with
  | zero => simpa using hx s
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact mulVec_bound M π _ B ih s

lemma evalUpdate_eq (M : MDP S A) (γ : ℝ) (π : Policy S A) (v : S → ℝ) :
    evalUpdate M γ π v = policyReward M π + γ • (policyTrans M π *ᵥ v) := by
  funext s
  simp only [evalUpdate, policyReward, policyTrans, MDP.expReward, MDP.trans, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  have h1 : ∀ a, ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s') =
      (∑ r ∈ M.R, r * ∑ s', M.p s a s' r) + γ * ∑ s', (∑ r ∈ M.R, M.p s a s' r) * v s' := by
    intro a
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [h1, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

lemma iterate_eq (M : MDP S A) (γ : ℝ) (π : Policy S A) (v₀ : S → ℝ) (k : ℕ) :
    (evalUpdate M γ π)^[k] v₀ =
      (∑ j ∈ Finset.range k, γ ^ j • (policyTrans M π ^ j *ᵥ policyReward M π)) +
        γ ^ k • (policyTrans M π ^ k *ᵥ v₀) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, evalUpdate_eq, Finset.sum_range_succ']
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_mulVec,
      smul_add, Finset.smul_sum, smul_smul, pow_succ', pow_zero, one_smul, Matrix.one_mulVec]
    abel

end SuttonBartoRL.DP.IPEAux

open SuttonBartoRL.DP in
theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A)
    (v₀ : S → ℝ) :
    Filter.Tendsto (fun k : ℕ => (evalUpdate M γ π)^[k] v₀) Filter.atTop
      (nhds (stateValue M γ π)) := by
  rw [tendsto_pi_nhds]
  intro s
  simp_rw [IPEAux.iterate_eq]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  obtain ⟨B, hB⟩ : ∃ B, ∀ s, |policyReward M π s| ≤ B :=
    ⟨∑ s, |policyReward M π s|, fun s =>
      Finset.single_le_sum (f := fun s => |policyReward M π s|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ s)⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ s, |v₀ s| ≤ C :=
    ⟨∑ s, |v₀ s|, fun s =>
      Finset.single_le_sum (f := fun s => |v₀ s|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ s)⟩
  have hsum : Summable (fun j : ℕ => γ ^ j * (Matrix.mulVec (policyTrans M π ^ j) (policyReward M π)) s) := by
    refine Summable.of_norm_bounded (g := fun j : ℕ => B * γ ^ j)
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_left B) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 j), mul_comm]
    exact mul_le_mul_of_nonneg_right (IPEAux.pow_mulVec_bound M π _ B hB j s) (pow_nonneg hγ0 j)
  have h1 : Filter.Tendsto
      (fun k : ℕ => ∑ j ∈ Finset.range k, γ ^ j * (Matrix.mulVec (policyTrans M π ^ j) (policyReward M π)) s)
      Filter.atTop (nhds (stateValue M γ π s)) := by
    have := hsum.hasSum.tendsto_sum_nat
    simpa [stateValue, expectedRewardAt] using this
  have h2 : Filter.Tendsto (fun k : ℕ => γ ^ k * (Matrix.mulVec (policyTrans M π ^ k) (v₀)) s)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun k : ℕ => C * γ ^ k) (fun k => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 k), mul_comm]
      exact mul_le_mul_of_nonneg_right (IPEAux.pow_mulVec_bound M π _ C hC k s) (pow_nonneg hγ0 k)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).const_mul C
  simpa using h1.add h2
