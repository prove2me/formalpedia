-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSeedABI.budgeted_header
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:50:52.0112+00:00
-- url     : https://prove2.me/submissions/1d2582ef-569b-40eb-adf3-d20c83805d8d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredSeedABI

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSeedABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish
open LightWeightedGlobalColoredInitializationProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSeedABI
theorem _root_.solution (C : Config) (seedCount newSpan K bDigit n nO : ℕ) :
    budgetedValues (header C seedCount 1 1 1 0 0 0 newSpan) K bDigit n C.J nO=
      header C seedCount 1 1 1 (n^2) (n^2) (LightTernaryInitialBudgets.initial K bDigit n C.J nO) newSpan := by
  simp only [Nat.pow_two]
  rfl

end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSeedABI
