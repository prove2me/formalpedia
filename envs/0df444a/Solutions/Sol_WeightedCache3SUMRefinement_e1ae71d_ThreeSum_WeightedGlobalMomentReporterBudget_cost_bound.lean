-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget.cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:22:22.850733+00:00
-- url     : https://prove2.me/submissions/f78156dc-3dfe-4e04-9aec-81dc5a50ca66

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentReporterBudget_fold_floor
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentReporterBudget_fold_member

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (terms : ℕ) (c : ℕ×ℕ) (hc : c∈channels terms) :
    LightWeightedGlobalCertifiedMomentDriver.cost S c≤weightBudget terms*base S := by
  have hC : 1000≤weightBudget terms := fold_floor _
  have hcC : circuitCost c≤weightBudget terms := fold_member _ c hc
  have hL : ((leftMoment c.1 c.2).compile LightTernaryScalarChannel.atoms).cost+12≤weightBudget terms := by
    unfold circuitCost at hcC
    omega
  have hR : ((rightMoment c.1 c.2).compile LightTernaryScalarChannel.atoms).cost+12≤weightBudget terms := by
    unfold circuitCost at hcC
    omega
  have hl := Nat.mul_le_mul_left S.left.NL hL
  have hr := Nat.mul_le_mul_left S.right.NL hR
  have hq := Nat.mul_le_mul_right S.front.count (show 24≤weightBudget terms by omega)
  have ht := Nat.mul_le_mul_right S.runtime (show 1≤weightBudget terms by omega)
  unfold LightWeightedGlobalCertifiedMomentDriver.cost LightTernaryMomentChannelStep.time
    LightTernaryScalarChannel.time LightTernaryMomentAccumulate.time base
  nlinarith only [hl,hr,hq,ht,hC]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
