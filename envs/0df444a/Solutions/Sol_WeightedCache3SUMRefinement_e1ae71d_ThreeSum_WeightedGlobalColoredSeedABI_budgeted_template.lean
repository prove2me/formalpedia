-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSeedABI.budgeted_template
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:26:35.604991+00:00
-- url     : https://prove2.me/submissions/df4c5934-9cc6-45fc-bf97-18ed546fc599

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredInitializationProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaInitialSeedHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredSeedABI
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredSeedABI_budgeted_header
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredSeedABI_template

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
theorem _root_.solution (I : Input) (A : Inputs) (p n U R F q K bDigit : ℕ)
    (hleft : A.leftTagged=A.Bmatrix) (hright : A.rightTagged=A.Cmatrix) :
    budgetedValues (LightWeightedGlobalArenaTemplate.seedValues
      (frame (values n U I.free A.Bmatrix I.nB A.Cmatrix I.nC A.Omatrix I.requesterCount A.positions A.menu A.J p R F q))
      I.free I.capacity) K bDigit n A.J I.requesterCount=
      header (config p 0 I A 0) (q*q) 1 1 1 (n^2) (n^2)
        (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount) (addr I.free I.capacity 8) :=by
  rw [template I A p n U R F q hleft hright]
  exact budgeted_header _ _ _ _ _ _ _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSeedABI
