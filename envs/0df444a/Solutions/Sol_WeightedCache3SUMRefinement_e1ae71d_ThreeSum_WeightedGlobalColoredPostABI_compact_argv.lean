-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI.compact_argv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:08.996807+00:00
-- url     : https://prove2.me/submissions/7f273d85-d02e-4a33-9e27-6c6a1ef7933d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPostABI

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI
theorem _root_.solution {p m F r : ℕ} [Fact p.Prime]
    (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : WeightedGlobalArenaSourceSetup.Input) (nB nC : ℕ) :
    (LightWeightedGlobalCompactReporter.zeroCounts
      (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q {I with nB:=nB,nC:=nC})).argv=
    (LightWeightedGlobalCompactReporter.zeroCounts
      (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q I)).argv := by rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPostABI
