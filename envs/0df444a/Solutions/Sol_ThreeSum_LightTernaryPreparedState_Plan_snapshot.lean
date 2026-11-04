-- Prove2me | solution 1 for ThreeSum.LightTernaryPreparedState.Plan.snapshot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:44:35.349231+00:00
-- url     : https://prove2.me/submissions/53c1728f-ad28-46f4-bd8e-e0837688e389

import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedWanted
import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedState

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
open ThreeSum.LightTernaryPreparedWanted
set_option maxHeartbeats 6000000
namespace ThreeSum.LightTernaryPreparedState
namespace Plan
theorem _root_.solution {lim : Limits} {N out bankValues caps : ℕ} {f g : Config}
    {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb} {F G : TritWord N→ℤ}
    (R : Plan lim out bankValues caps f g Q E F G)
    (hbank : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ))
    (hF : ∀ j<f.nb, μ (f.bv+j)=binomialZeta F (E.word j))
    (hG : ∀ j<f.nb, μ (g.bv+j)=binomialZeta G (E.word j))
    (hH : LightTernaryBankSweep.Stages E
      (fun k => stageValue k (LightTernaryWantedQuery.H F G)) bankValues N μ) :
    Snapshot lim out bankValues caps f g μ Q E F G := by
  exact { R with bankRead := hbank, Fbank := hF, Gbank := hG, Hbank := hH }
end Plan
end ThreeSum.LightTernaryPreparedState
