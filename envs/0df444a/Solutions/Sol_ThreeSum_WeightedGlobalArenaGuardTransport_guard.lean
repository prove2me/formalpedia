-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaGuardTransport.guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:04:11.656274+00:00
-- url     : https://prove2.me/submissions/a75672d6-f834-40a8-adcb-22cd10e25a09

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaGuardTransport
import Theorems.Thm_ThreeSum_WeightedGlobalArenaGuardTransport_primitive
import Theorems.Thm_ThreeSum_WeightedGlobalArenaGuardTransport_tensor
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateGuard_guard
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaGuardTransport
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalArenaGuardTransport
theorem _root_.solution {lim : Limits} {depth K U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ ν : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (M : WeightedGlobalArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (G : WeightedGlobalArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D μ L R)
    (B : WeightedGlobalArenaCandidateGuard.Resources (lim := lim) (depth := depth) (positionCap := positionCap) maps τ I A D)
    (h : KeepInputs I μ ν) (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hτ : 0<τ) (hraw : 1≤(WeightedGlobalGoodOutputCatalog.raws maps τ).length)
    (hpaired : |(WeightedGlobalArenaCandidateGuard.actual maps τ cap U Q I A seed D L R).score K|≤lim.word) :
    (WeightedGlobalArenaCandidateGuard.actual maps τ cap U Q I A seed D L R).Guard lim depth K (4^fixedLength m) F
      (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
      (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) ν := by
  exact WeightedGlobalArenaCandidateGuard.guard maps τ cap Q I A D ν L R
    (primitive M h G.headerCells G.nB G.nC B.requester B.catalog)
    (tensor G h hprefix) B hτ hraw hpaired
end ThreeSum.WeightedGlobalArenaGuardTransport
