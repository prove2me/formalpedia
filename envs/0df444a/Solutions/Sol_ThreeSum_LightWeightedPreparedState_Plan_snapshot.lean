-- Prove2me | solution 1 for ThreeSum.LightWeightedPreparedState.Plan.snapshot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:45:08.872924+00:00
-- url     : https://prove2.me/submissions/cdd30eb9-8283-4c02-a04b-31d3ebbc2e60

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_PreparedState

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.LightWeightedPreparedWanted
set_option maxHeartbeats 6000000
namespace ThreeSum.LightWeightedPreparedState
namespace Plan
theorem _root_.solution {lim : Limits} {N out bankValues caps : ℕ} {f g : Config}
    {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb} {F G : TritWord N→ℤ}
    (R : Plan lim out bankValues caps f g Q E F G)
    (hbank : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ))
    (hF : ∀ j<f.nb, μ (f.bv+j)=binomialZeta F (E.word j))
    (hG : ∀ j<f.nb, μ (g.bv+j)=binomialZeta G (E.word j))
    (hH : LightWeightedBankSweep.Stages E
      (fun k => stageValue k (LightWeightedWantedQuery.H F G)) bankValues N μ) :
    Snapshot lim out bankValues caps f g μ Q E F G := by
  exact { R with bankRead := hbank, Fbank := hF, Gbank := hG, Hbank := hH }
end Plan
end ThreeSum.LightWeightedPreparedState
