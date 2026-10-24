-- Prove2me | solution 1 for PandoraBO.Private20261023.policy_terminal_measurable_integrable
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:54:01.893645+00:00
-- url     : https://prove2.me/submissions/259f4471-9df7-4af9-b175-5320f8932c02

import Definitions.Def_PandoraBO_Model
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Group.Arithmetic

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

namespace PandoraBO.Private20261023

-- Fold signatures contain conditionals on occupied histories.
attribute [local instance] Classical.propDecidable

private theorem measurable_selection {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι]
    (f : ι → α → β) (hf : ∀ i, Measurable (f i))
    (g : α → ι) (hg : Measurable g) :
    Measurable (fun x => f (g x) x) := by
  have h : Measurable (fun p : α × ι => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hg)

theorem initialHistory_measurable {n : ℕ} (π : Policy n) :
    Measurable (initialHistory π) := by
  have hfirst : Measurable (fun ω : Outcome n => π.first ω.2) :=
    π.first_measurable.comp measurable_snd
  have hreward : Measurable (fun ω : Outcome n => ω.1 (π.first ω.2)) :=
    measurable_selection (fun i : Box n => fun ω : Outcome n => ω.1 i)
      (fun i => (measurable_pi_apply i).comp measurable_fst)
      (fun ω : Outcome n => π.first ω.2) hfirst
  apply measurable_pi_lambda
  intro k
  by_cases hk : k = 0
  · simpa only [initialHistory, if_pos hk] using
      ((measurable_const : Measurable (fun _ : Outcome n => true)).prodMk
        (hfirst.prodMk hreward))
  · simpa only [initialHistory, if_neg hk] using
      (measurable_const : Measurable (fun _ : Outcome n =>
        (false, (0 : Box n), (0 : ℝ))))

theorem rolloutAux_measurable {n : ℕ} (π : Policy n) (fuel step : ℕ)
    (h : Outcome n → History n) (hh : Measurable h) :
    Measurable (fun ω => rolloutAux π ω fuel step (h ω)) := by
  classical
  induction fuel generalizing step h with
  | zero => exact hh
  | succ fuel ih =>
      let branch : Decision n → Outcome n → History n := fun d ω =>
        match d with
        | none => h ω
        | some i =>
            if hs : step < n + 1 then
              rolloutAux π ω fuel (step + 1)
                (Function.update (h ω) ⟨step, hs⟩ (true, i, ω.1 i))
            else h ω
      have hbranch : ∀ d, Measurable (branch d) := by
        intro d
        cases d with
        | none => exact hh
        | some i =>
            by_cases hs : step < n + 1
            · have hnew : Measurable (fun ω : Outcome n =>
                  Function.update (h ω) (⟨step, hs⟩ : Fin (n + 1))
                    (true, i, ω.1 i)) :=
                (measurable_update' (a := (⟨step, hs⟩ : Fin (n + 1)))).comp
                  (hh.prodMk (measurable_const.prodMk
                    (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_fst))))
              simpa only [branch, dif_pos hs] using ih (step + 1) _ hnew
            · simpa only [branch, dif_neg hs] using hh
      have hd : Measurable (fun ω : Outcome n => π.next (h ω, ω.2)) :=
        π.next_measurable.comp (hh.prodMk measurable_snd)
      have hm := measurable_selection branch hbranch (fun ω => π.next (h ω, ω.2)) hd
      have heq : (fun ω => branch (π.next (h ω, ω.2)) ω) =
          (fun ω => rolloutAux π ω (fuel + 1) step (h ω)) := by
        funext ω
        cases hd' : π.next (h ω, ω.2) with
        | none => simp only [branch, rolloutAux, hd']
        | some i =>
            by_cases hs : step < n + 1
            · simp only [branch, rolloutAux, hd', dif_pos hs]
            · simp only [branch, rolloutAux, hd', dif_neg hs]
      exact heq ▸ hm

theorem terminalHistory_measurable {n : ℕ} (π : Policy n) :
    Measurable (terminalHistory π) :=
  rolloutAux_measurable π n 1 (initialHistory π) (initialHistory_measurable π)

theorem occupied_measurableSet {n : ℕ} (k : Fin (n + 1)) :
    MeasurableSet {h : History n | occupied h k} := by
  exact (measurable_pi_apply k).fst (measurableSet_singleton true)

theorem observedReward_measurable {n : ℕ} (k : Fin (n + 1)) :
    Measurable (fun h : History n => observedReward h k) :=
  (measurable_pi_apply k).snd.snd

private theorem historyFold_measurable {n : ℕ} (ks : List (Fin (n + 1)))
    (v : History n → ℝ) (hv : Measurable v) :
    Measurable (fun h => ks.foldl (fun incumbent k =>
      if occupied h k then max incumbent (observedReward h k) else incumbent) (v h)) := by
  classical
  induction ks generalizing v with
  | nil => exact hv
  | cons k ks ih =>
      simp only [List.foldl_cons]
      apply ih
      exact Measurable.ite (occupied_measurableSet k)
        (hv.max (observedReward_measurable k)) hv

theorem historyReward_measurable {n : ℕ} :
    Measurable (historyReward : History n → ℝ) :=
  historyFold_measurable (List.finRange (n + 1))
    (fun h => observedReward h 0) (observedReward_measurable 0)

theorem historyCost_measurable {n : ℕ} (M : Instance n) :
    Measurable (historyCost M) := by
  classical
  apply Finset.measurable_sum
  intro k hk
  exact Measurable.ite (occupied_measurableSet k)
    ((measurable_of_finite M.cost).comp (measurable_pi_apply k).snd.fst)
    measurable_const

theorem terminalReward_measurable {n : ℕ} (π : Policy n) :
    Measurable (terminalReward π) :=
  historyReward_measurable.comp (terminalHistory_measurable π)

theorem terminalCost_measurable {n : ℕ} (M : Instance n) (π : Policy n) :
    Measurable (terminalCost M π) :=
  (historyCost_measurable M).comp (terminalHistory_measurable π)

theorem terminalReward_integrable {n : ℕ} (M : Instance n) (π : Policy n) :
    Integrable (terminalReward π) (jointLaw M) := by
  apply (rewardEnvelope_integrable M).mono' (terminalReward_measurable π).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    simpa only [Real.norm_eq_abs] using terminalReward_abs_le π ω)

theorem terminalCost_integrable {n : ℕ} (M : Instance n) (π : Policy n) :
    Integrable (terminalCost M π) (jointLaw M) := by
  letI : IsProbabilityMeasure (jointLaw M) := jointLaw_probability M
  apply (integrable_const (uniformCostBound M)).mono'
    (terminalCost_measurable M π).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    simpa only [Real.norm_eq_abs] using terminalCost_abs_le M π ω)

theorem policy_terminal_measurable_integrable_core {n : ℕ} (M : Instance n) (π : Policy n) :
    Measurable (terminalReward π) ∧ Measurable (terminalCost M π) ∧
      Integrable (terminalReward π) (jointLaw M) ∧
      Integrable (terminalCost M π) (jointLaw M) := by
  exact ⟨terminalReward_measurable π, terminalCost_measurable M π,
    terminalReward_integrable M π, terminalCost_integrable M π⟩

end PandoraBO.Private20261023


theorem solution {n : ℕ} (M : PandoraBO.Instance n) (π : PandoraBO.Policy n) :
    Measurable (PandoraBO.terminalReward π) ∧
    Measurable (PandoraBO.terminalCost M π) ∧
    Integrable (PandoraBO.terminalReward π) (PandoraBO.jointLaw M) ∧
    Integrable (PandoraBO.terminalCost M π) (PandoraBO.jointLaw M) := by
  exact PandoraBO.Private20261023.policy_terminal_measurable_integrable_core M π
