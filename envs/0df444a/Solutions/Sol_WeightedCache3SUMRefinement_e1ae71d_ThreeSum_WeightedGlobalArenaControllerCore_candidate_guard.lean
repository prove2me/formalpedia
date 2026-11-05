-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerCore.candidate_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:19:02.703277+00:00
-- url     : https://prove2.me/submissions/f879afe6-6a25-4959-83a8-92b197d2b26e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaGuardTransport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerPlan
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerCore
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaCandidateGuard_guard
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaGuardTransport_guard
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaGuardTransport_tensor
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_reads
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_resources


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerCore
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerCore
theorem _root_.solution {lim : Limits} {depth K U n positionCap : ℕ}
    {maps : Fin F→Weight m p} {τ cap : ℕ} {Q : WeightedGlobalGoodOutputCatalog.Output m}
    {I : Input} {A : Inputs} {D : (seed : ℕ)→Data (config p r I A seed)}
    {μ ν : ℕ→ℤ} {L R : ℕ→ℕ→ℤ}
    (H : InputsReady (lim := lim) (depth := depth) (K := K) (U := U) (n := n) (positionCap := positionCap)
      maps τ cap Q I A D μ L R)
    (i : ℕ) (hi : i < n) (h : KeepInputs I μ ν) :
    ((family maps τ cap U Q I A D L R).candidate i).Guard lim (depth+1) K
      (4^fixedLength m) F (WeightedGlobalGoodOutputCatalog.raws maps τ)
      (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) ν := by
  exact WeightedGlobalArenaGuardTransport.guard maps τ cap Q I A (D i) μ ν L R
    (H.reads i hi) (H.tensor i hi) (H.resources i hi) h H.prefixAt H.threshold H.nonempty (H.pairedWord i hi)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerCore
