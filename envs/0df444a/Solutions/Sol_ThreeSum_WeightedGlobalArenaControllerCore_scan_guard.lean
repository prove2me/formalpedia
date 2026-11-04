-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaControllerCore.scan_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:57:54.19946+00:00
-- url     : https://prove2.me/submissions/7e53a00c-edec-4e76-808c-2d3094362681

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaGuardTransport
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Theorems.Thm_ThreeSum_WeightedGlobalArenaControllerCore_candidate_guard
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaControllerCore
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalArenaControllerCore
theorem _root_.solution {lim : Limits} {depth K U n positionCap i : ℕ}
    {maps : Fin F→Weight m p} {τ cap : ℕ} {Q : WeightedGlobalGoodOutputCatalog.Output m}
    {I : Input} {A : Inputs} {D : (seed : ℕ)→Data (config p r I A seed)}
    {μ ν : ℕ→ℤ} {L R : ℕ→ℕ→ℤ}
    (H : InputsReady (lim := lim) (depth := depth) (K := K) (U := U) (n := n) (positionCap := positionCap)
      maps τ cap Q I A D μ L R)
    (hi : i < n)
    (h : Invariant I (values (family maps τ cap U Q I A D L R) K) μ i ν) :
    ((family maps τ cap U Q I A D L R).candidate i).Guard lim (depth+1) K
      (4^fixedLength m) F (WeightedGlobalGoodOutputCatalog.raws maps τ)
      (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) ν :=
  candidate_guard H i hi h.1
end ThreeSum.WeightedGlobalArenaControllerCore
