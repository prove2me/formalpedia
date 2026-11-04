-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredPostABI.compact_argv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:10:46.707196+00:00
-- url     : https://prove2.me/submissions/657a76eb-6472-45c7-a6e6-68e1c6910a4b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000
namespace ThreeSum.WeightedGlobalColoredPostABI
theorem _root_.solution {p m F r : ℕ} [Fact p.Prime]
    (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : WeightedGlobalArenaSourceSetup.Input) (nB nC : ℕ) :
    (LightWeightedGlobalCompactReporter.zeroCounts
      (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q {I with nB:=nB,nC:=nC})).argv=
    (LightWeightedGlobalCompactReporter.zeroCounts
      (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q I)).argv := by rfl
end ThreeSum.WeightedGlobalColoredPostABI
