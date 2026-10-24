-- Prove2me | solution 1 for PandoraBO.Private20261023.policy_expectation_bounds_and_slater
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:53:41.211588+00:00
-- url     : https://prove2.me/submissions/5c3829fc-d455-48b6-87cb-580ac0bbf991

import Definitions.Def_PandoraBO_Model
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Policy bounds and explicit strict-feasibility witnesses

This file proves the uniform expectation bounds and deterministic one-box
policies needed by the dual analysis. The cost bound deliberately allows a
larger constant than the sharp total cost, so its proof does not depend on
separate no-repeat invariants for the rollout.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace PandoraBO.Private20261023

-- Fold signatures contain conditionals on occupied histories.
attribute [local instance] Classical.propDecidable

theorem seedLaw_probability : IsProbabilityMeasure seedLaw := by
  constructor
  simp [seedLaw, Real.volume_Icc]

theorem jointLaw_probability {n : ℕ} (M : Instance n) :
    IsProbabilityMeasure (jointLaw M) := by
  letI : ∀ i, IsProbabilityMeasure (M.law i) := M.law_probability
  letI : IsProbabilityMeasure seedLaw := seedLaw_probability
  dsimp [jointLaw]
  infer_instance

/-- Open one fixed box, then stop. -/
def singleBoxPolicy {n : ℕ} (i : Box n) : Policy n where
  first := fun _ => i
  first_measurable := measurable_const
  next := fun _ => none
  next_measurable := measurable_const
  next_unopened := by
    intro h u j hj
    cases hj

theorem singleBoxPolicy_rollout {n : ℕ} (i : Box n) (ω : Outcome n)
    (fuel step : ℕ) (h : History n) :
    rolloutAux (singleBoxPolicy i) ω fuel step h = h := by
  cases fuel <;> rfl

theorem singleBoxPolicy_terminalCost {n : ℕ} (M : Instance n)
    (i : Box n) (ω : Outcome n) :
    terminalCost M (singleBoxPolicy i) ω = M.cost i := by
  classical
  unfold terminalCost terminalHistory
  rw [singleBoxPolicy_rollout]
  unfold historyCost
  calc
    (∑ k : Fin (n + 1),
        if occupied (initialHistory (singleBoxPolicy i) ω) k then
          M.cost (observedBox (initialHistory (singleBoxPolicy i) ω) k) else 0)
      = ∑ k : Fin (n + 1), if k = 0 then M.cost i else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hk0 : k = 0 <;>
          simp [occupied, observedBox, initialHistory, singleBoxPolicy, hk0]
    _ = M.cost i := by simp

theorem singleBoxPolicy_expectedCost {n : ℕ} (M : Instance n) (i : Box n) :
    expectedCost M (singleBoxPolicy i) = M.cost i := by
  letI : IsProbabilityMeasure (jointLaw M) := jointLaw_probability M
  simp [expectedCost, singleBoxPolicy_terminalCost]

/-- A common, integrable envelope for every policy's terminal reward. -/
def rewardEnvelope {n : ℕ} (ω : Outcome n) : ℝ :=
  ∑ i : Box n, |ω.1 i|

theorem rewardEnvelope_nonneg {n : ℕ} (ω : Outcome n) :
    0 ≤ rewardEnvelope ω :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem coordinate_abs_le_rewardEnvelope {n : ℕ} (ω : Outcome n) (i : Box n) :
    |ω.1 i| ≤ rewardEnvelope ω := by
  exact Finset.single_le_sum (fun j _ => abs_nonneg (ω.1 j)) (Finset.mem_univ i)

theorem rewardCoordinate_integrable {n : ℕ} (M : Instance n) (i : Box n) :
    Integrable (fun ω : Outcome n => ω.1 i) (jointLaw M) := by
  letI : ∀ j, IsProbabilityMeasure (M.law j) := M.law_probability
  letI : IsProbabilityMeasure seedLaw := seedLaw_probability
  have heval : MeasurePreserving (fun ω : Outcome n => ω.1 i)
      (jointLaw M) (M.law i) := by
    simpa only [jointLaw, Function.comp_def, Function.eval] using
      (measurePreserving_eval M.law i).comp
        (measurePreserving_fst (μ := Measure.pi M.law) (ν := seedLaw))
  simpa only [Function.comp_def] using
    heval.integrable_comp_of_integrable (M.reward_integrable i)

theorem rewardEnvelope_integrable {n : ℕ} (M : Instance n) :
    Integrable (rewardEnvelope : Outcome n → ℝ) (jointLaw M) := by
  exact integrable_finsetSum Finset.univ
    (fun i _ => (rewardCoordinate_integrable M i).abs)

/-- Every stored reward remains bounded by any bound on the sampled rewards. -/
theorem rollout_reward_bound {n : ℕ} (π : Policy n) (ω : Outcome n)
    (S : ℝ) (hω : ∀ i : Box n, |ω.1 i| ≤ S)
    (fuel step : ℕ) (h : History n)
    (hh : ∀ k, |observedReward h k| ≤ S) :
    ∀ k, |observedReward (rolloutAux π ω fuel step h) k| ≤ S := by
  induction fuel generalizing step h with
  | zero => exact hh
  | succ fuel ih =>
      cases hd : π.next (h, ω.2) with
      | none => simpa only [rolloutAux, hd] using hh
      | some i =>
          by_cases hs : step < n + 1
          · simp only [rolloutAux, hd, dif_pos hs]
            apply ih
            intro k
            by_cases hk : k = (⟨step, hs⟩ : Fin (n + 1))
            · subst k
              simpa only [observedReward, Function.update_self] using hω i
            · simpa only [observedReward, Function.update_of_ne hk] using hh k
          · simpa only [rolloutAux, hd, dif_neg hs] using hh

theorem initialHistory_reward_bound {n : ℕ} (π : Policy n) (ω : Outcome n) :
    ∀ k, |observedReward (initialHistory π ω) k| ≤ rewardEnvelope ω := by
  intro k
  by_cases hk : k = 0
  · simpa only [observedReward, initialHistory, if_pos hk] using
      coordinate_abs_le_rewardEnvelope ω (π.first ω.2)
  · simpa only [observedReward, initialHistory, if_neg hk, abs_zero] using
      rewardEnvelope_nonneg ω

private theorem fold_reward_abs_le {n : ℕ} (h : History n) (S : ℝ)
    (hh : ∀ k, |observedReward h k| ≤ S)
    (ks : List (Fin (n + 1))) (v : ℝ) (hv : |v| ≤ S) :
    |ks.foldl (fun incumbent k =>
      if occupied h k then max incumbent (observedReward h k) else incumbent) v| ≤ S := by
  classical
  induction ks generalizing v with
  | nil => exact hv
  | cons k ks ih =>
      simp only [List.foldl_cons]
      apply ih
      split_ifs with hk
      · exact abs_le.mpr
          ⟨(abs_le.mp hv).1.trans (le_max_left _ _),
            max_le (abs_le.mp hv).2 (abs_le.mp (hh k)).2⟩
      · exact hv

theorem historyReward_abs_le {n : ℕ} (h : History n) (S : ℝ)
    (hh : ∀ k, |observedReward h k| ≤ S) : |historyReward h| ≤ S := by
  exact fold_reward_abs_le h S hh (List.finRange (n + 1)) (observedReward h 0) (hh 0)

theorem terminalReward_abs_le {n : ℕ} (π : Policy n) (ω : Outcome n) :
    |terminalReward π ω| ≤ rewardEnvelope ω := by
  apply historyReward_abs_le
  exact rollout_reward_bound π ω (rewardEnvelope ω)
    (coordinate_abs_le_rewardEnvelope ω) n 1 (initialHistory π ω)
    (initialHistory_reward_bound π ω)

theorem expectedReward_abs_le {n : ℕ} (M : Instance n) (π : Policy n) :
    |expectedReward M π| ≤ ∫ ω, rewardEnvelope ω ∂jointLaw M := by
  have h := norm_integral_le_of_norm_le (f := terminalReward π) (rewardEnvelope_integrable M)
    (ae_of_all _ (fun ω => by
      simpa only [Real.norm_eq_abs] using terminalReward_abs_le π ω))
  simpa only [expectedReward, Real.norm_eq_abs] using h

/-- A deliberately non-sharp uniform cost bound, sufficient for dual analysis. -/
def uniformCostBound {n : ℕ} (M : Instance n) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * ∑ i : Box n, M.cost i

theorem totalCost_nonneg {n : ℕ} (M : Instance n) :
    0 ≤ ∑ i : Box n, M.cost i :=
  Finset.sum_nonneg (fun i _ => (M.cost_positive i).le)

theorem uniformCostBound_nonneg {n : ℕ} (M : Instance n) :
    0 ≤ uniformCostBound M :=
  mul_nonneg (Nat.cast_nonneg _) (totalCost_nonneg M)

theorem historyCost_nonneg {n : ℕ} (M : Instance n) (h : History n) :
    0 ≤ historyCost M h := by
  classical
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact (M.cost_positive _).le
  · exact le_rfl

theorem historyCost_le_uniform {n : ℕ} (M : Instance n) (h : History n) :
    historyCost M h ≤ uniformCostBound M := by
  classical
  unfold historyCost uniformCostBound
  calc
    (∑ k : Fin (n + 1), if occupied h k then M.cost (observedBox h k) else 0)
        ≤ ∑ _k : Fin (n + 1), ∑ i : Box n, M.cost i := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs
      · exact Finset.single_le_sum (fun i _ => (M.cost_positive i).le)
          (Finset.mem_univ (observedBox h k))
      · exact totalCost_nonneg M
    _ = ((n + 1 : ℕ) : ℝ) * ∑ i : Box n, M.cost i := by simp

theorem terminalCost_abs_le {n : ℕ} (M : Instance n) (π : Policy n) (ω : Outcome n) :
    |terminalCost M π ω| ≤ uniformCostBound M := by
  unfold terminalCost
  rw [abs_of_nonneg (historyCost_nonneg M (terminalHistory π ω))]
  exact historyCost_le_uniform M (terminalHistory π ω)

theorem expectedCost_abs_le {n : ℕ} (M : Instance n) (π : Policy n) :
    |expectedCost M π| ≤ uniformCostBound M := by
  letI : IsProbabilityMeasure (jointLaw M) := jointLaw_probability M
  have h := norm_integral_le_of_norm_le_const (f := terminalCost M π)
    (ae_of_all (jointLaw M) (fun ω => by
      simpa only [Real.norm_eq_abs] using terminalCost_abs_le M π ω))
  simpa only [expectedCost, Real.norm_eq_abs, probReal_univ, mul_one] using h

theorem expectedCost_nonneg {n : ℕ} (M : Instance n) (π : Policy n) :
    0 ≤ expectedCost M π :=
  integral_nonneg (fun ω => historyCost_nonneg M (terminalHistory π ω))

/-- The exact foundation required by the coercive dual-envelope argument. -/
theorem policy_expectation_bounds_and_slater_core {n : ℕ} (M : Instance n) :
    (∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧
      ∀ π : Policy n, |expectedReward M π| ≤ R ∧ |expectedCost M π| ≤ C) ∧
    (∀ i : Box n, ∃ π : Policy n, expectedCost M π = M.cost i) := by
  constructor
  · refine ⟨∫ ω, rewardEnvelope ω ∂jointLaw M, uniformCostBound M,
      integral_nonneg rewardEnvelope_nonneg, uniformCostBound_nonneg M, ?_⟩
    intro π
    exact ⟨expectedReward_abs_le M π, expectedCost_abs_le M π⟩
  · intro i
    exact ⟨singleBoxPolicy i, singleBoxPolicy_expectedCost M i⟩

end PandoraBO.Private20261023

theorem solution {n : ℕ} (M : PandoraBO.Instance n) :
    (∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧
      ∀ π : PandoraBO.Policy n,
        |PandoraBO.expectedReward M π| ≤ R ∧ |PandoraBO.expectedCost M π| ≤ C) ∧
    (∀ i : PandoraBO.Box n, ∃ π : PandoraBO.Policy n,
      PandoraBO.expectedCost M π = M.cost i) := by
  exact PandoraBO.Private20261023.policy_expectation_bounds_and_slater_core M
