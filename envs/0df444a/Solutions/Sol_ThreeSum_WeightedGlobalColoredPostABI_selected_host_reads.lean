-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredPostABI.selected_host_reads
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:50:24.220123+00:00
-- url     : https://prove2.me/submissions/23cf276b-588d-4202-afdf-f9c3d137e5df

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
import Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_argv_zeroCounts_get
import Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_selected_argv

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
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ) (host : ℕ)
    (hhost : Seg μ host (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q
      (WeightedGlobalArenaNativeComplete.input I U radix nA H A B C)).argv) :
    ∀i<106,i≠11→i≠34→μ (host+i)=
      (LightWeightedGlobalCompactReporter.zeroCounts (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q
        (WeightedGlobalArenaPostSelection.selectedInput I U radix nA H A B C keysB keysC))).argv.getD i 0 := by
  intro i hi h11 h34
  rw [selected_argv,argv_zeroCounts_get _ i hi h11 h34]
  have hil : i<(WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q
      (WeightedGlobalArenaNativeComplete.input I U radix nA H A B C)).argv.length := hi
  rw [List.getD_eq_getElem _ _ hil]
  exact hhost i hil
end ThreeSum.WeightedGlobalColoredPostABI
