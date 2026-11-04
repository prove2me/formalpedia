-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredPostABI.selected_argv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:10:45.200137+00:00
-- url     : https://prove2.me/submissions/5d6f6482-afae-4cfc-bd4f-d10b158d1acd

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
theorem _root_.solution {p m F r J : ℕ} [Fact p.Prime]
    (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : WeightedGlobalArenaSourceSetup.Input)
    (U radix nA : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    (LightWeightedGlobalCompactReporter.zeroCounts (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q
      (WeightedGlobalArenaPostSelection.selectedInput I U radix nA H A B C keysB keysC))).argv=
    (LightWeightedGlobalCompactReporter.zeroCounts (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q
      (WeightedGlobalArenaNativeComplete.input I U radix nA H A B C))).argv := by rfl
end ThreeSum.WeightedGlobalColoredPostABI
