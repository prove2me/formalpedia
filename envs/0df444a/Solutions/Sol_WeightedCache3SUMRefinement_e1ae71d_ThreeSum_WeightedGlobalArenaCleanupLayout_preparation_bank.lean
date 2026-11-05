-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCleanupLayout.preparation_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:01:26.369132+00:00
-- url     : https://prove2.me/submissions/f7a6be64-bd7e-4814-a7e5-7d783a84bff5

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupLayout

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCleanupLayout
open Light WeightedGlobalArenaLayout LightOriginalSurvivors LightOriginalSurvivorPair
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCleanupLayout
theorem _root_.solution {free C q L : ℕ}
    {μ ν : ℕ→ℤ} (hL : L+1≤C) (hq : q≤C)
    (h : ∀ x,LightTernaryFinalPreparation.Unwritten (addr free C 6) L
      (addr free C 7) (addr free C 8) q x→ν x=μ x)
    {x : ℕ} (hx : addr free C 9≤x) : ν x=μ x := by
  apply h
  unfold LightTernaryFinalPreparation.Unwritten addr at *
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCleanupLayout
