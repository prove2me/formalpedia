-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaCandidateGuard.guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:52:15.363405+00:00
-- url     : https://prove2.me/submissions/ba52856d-f13e-4ed8-bc01-21771b9b01f1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Theorems.Thm_ThreeSum_LightTernaryQueryPlan_ready
import Theorems.Thm_ThreeSum_LightWeightedQueryPlan_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedPrimitiveGuards_guards
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedScoreReady_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorReady_ready


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCandidateGuard
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaCandidateGuard
theorem _root_.solution {lim : Limits} {depth K U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (M : WeightedGlobalArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (G : WeightedGlobalArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D μ L R)
    (B : Resources (lim := lim) (depth := depth) (positionCap := positionCap) maps τ I A D)
    (hτ : 0<τ) (hraw : 1≤(WeightedGlobalGoodOutputCatalog.raws maps τ).length)
    (hpaired : |(actual maps τ cap U Q I A seed D L R).score K|≤lim.word) :
    (actual maps τ cap U Q I A seed D L R).Guard lim depth K (4^fixedLength m) F
      (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
      (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) μ := by
  obtain ⟨ga,gs,gw,gc⟩ := WeightedGlobalArenaSeedPrimitiveGuards.guards maps τ I A D μ M
    G.wordSpace G.capacity.endSpace G.nB G.nC B.requester B.coordinates B.catalog B.histogram
    B.wanted B.divide B.word B.depth G.family hτ hraw
  exact ⟨WeightedGlobalArenaSeedScoreReady.ready maps τ cap Q I A D μ L R ga gs gw gc G B.seed,hpaired⟩
end ThreeSum.WeightedGlobalArenaCandidateGuard
