-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaCleanupLayout.preparation_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:29:06.427831+00:00
-- url     : https://prove2.me/submissions/426c5cca-e198-4094-85d9-7072172aed8b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCleanupLayout
open Light WeightedGlobalArenaLayout LightOriginalSurvivors LightOriginalSurvivorPair
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalArenaCleanupLayout
theorem _root_.solution {free C q L : ℕ}
    {μ ν : ℕ→ℤ} (hL : L+1≤C) (hq : q≤C)
    (h : ∀ x,LightTernaryFinalPreparation.Unwritten (addr free C 6) L
      (addr free C 7) (addr free C 8) q x→ν x=μ x)
    {x : ℕ} (hx : addr free C 9≤x) : ν x=μ x := by
  apply h
  unfold LightTernaryFinalPreparation.Unwritten addr at *
  omega
end ThreeSum.WeightedGlobalArenaCleanupLayout
