-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState.Plan.snapshot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:01:16.351195+00:00
-- url     : https://prove2.me/submissions/98285ffe-25b8-4f12-be11-ba2075626f05

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedState

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.LightWeightedPreparedWanted
set_option maxHeartbeats 6000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState
