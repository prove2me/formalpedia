-- Prove2me | solution 1 for PoursoltaniRegret.Objective.proposition_2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:14:19.152162+00:00
-- url     : https://prove2.me/submissions/9220c636-4bc8-46c5-b4b7-edde5a201a74

import Definitions.Def_PoursoltaniRegret_Objective_Regret
import Definitions.Def_PoursoltaniRegret_Objective_Lift

open Matrix
open PoursoltaniRegret.Objective

def modelCounterexample : Model 1 1 1 1 1 1 where
  W := 0
  v := 0
  P := 0
  q := 0
  A := 0
  B := 0
  psi := fun _ => 1
  c := 0
  D := 0
  d := 0

private lemma zero_mem_firstStage : (0 : Fin 1 → ℝ) ∈ modelCounterexample.firstStage := by
  intro i
  simp [modelCounterexample]

private lemma zero_mem_uncertainty : (0 : Fin 1 → ℝ) ∈ modelCounterexample.uncertainty := by
  intro i
  simp [modelCounterexample]

private lemma zero_mem_recourse (x : Fin 1 → ℝ) :
    (0 : Fin 1 → ℝ) ∈ modelCounterexample.recourse x := by
  intro i
  simp [modelCounterexample]

private lemma assumption1_model : modelCounterexample.assumption1 :=
  ⟨0, zero_mem_firstStage, 0, zero_mem_uncertainty, 0, zero_mem_recourse 0⟩

private lemma assumption2_model : modelCounterexample.assumption2 :=
  fun x _ _ _ => ⟨0, zero_mem_recourse x⟩

private lemma regretAt_zero_nonpos : modelCounterexample.regretAt 0 ≤ (0 : EReal) := by
  unfold Model.regretAt
  refine iSup_le fun z => iSup_le fun xb => iSup_le fun yb => ?_
  refine iInf_le_of_le ⟨0, zero_mem_recourse 0⟩ ?_
  simp [modelCounterexample, Model.recourseCost]

private lemma liftBestAt_zero_le_neg_one :
    modelCounterexample.liftBestAt 0 ≤ ((-1 : ℝ) : EReal) := by
  unfold Model.liftBestAt
  refine iSup_le fun pi => ?_
  unfold Model.liftPolicyValue
  let u0 : (Fin 1 → ℝ) × (Fin 1 → ℝ) := (0, fun _ => -1)
  have hu0 : u0 ∈ modelCounterexample.liftUncertainty := by
    refine ⟨zero_mem_uncertainty, ?_⟩
    ext i
    simp [modelCounterexample, u0, Model.recourseCost]
  refine iInf_le_of_le ⟨u0, hu0⟩ ?_
  have hpi : pi.val u0 ∈ modelCounterexample.liftRecourse u0 := pi.property u0 hu0
  have hnonneg : 0 ≤ (pi.val u0).1 0 := hpi.1 0
  have hprof : modelCounterexample.liftProfit 0 u0 (pi.val u0) ≤ -1 := by
    unfold Model.liftProfit
    simp [modelCounterexample, u0, dotProduct]
    linarith
  exact EReal.coe_le_coe_iff.mpr hprof

theorem solution : ¬ (∀ {nx ny nz m r s : ℕ} (M : Model nx ny nz m r s)
    (h1 : M.assumption1) (h2 : M.assumption2),
    (∀ x ∈ M.firstStage, M.regretAt x = -M.liftBestAt x) ∧
    M.regretValue = -M.liftValue ∧
    (∀ x, M.isRegretOptimal x ↔ M.isLiftFirstStageOptimal x) ∧
    ((M.assumption3 ∧ M.assumption5) →
      M.liftAssumption1 ∧ M.liftAssumption2 ∧ M.liftAssumption3) ∧
    ((M.assumption3 ∧ M.assumption5 ∧ M.assumption4) → M.liftAssumption4)) := by
  intro h
  have hreg := (h modelCounterexample assumption1_model assumption2_model).1 0 zero_mem_firstStage
  have h1 : ((1 : ℝ) : EReal) ≤ -modelCounterexample.liftBestAt 0 := by
    have hneg := EReal.neg_le_neg_iff.mpr liftBestAt_zero_le_neg_one
    simpa using hneg
  rw [← hreg] at h1
  have h_contra : ((1 : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := le_trans h1 regretAt_zero_nonpos
  have h_real : (1 : ℝ) ≤ (0 : ℝ) := EReal.coe_le_coe_iff.mp h_contra
  linarith
