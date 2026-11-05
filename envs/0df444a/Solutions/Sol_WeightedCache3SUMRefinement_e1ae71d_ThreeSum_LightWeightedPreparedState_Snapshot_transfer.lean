-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState.Snapshot.transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:01:50.068862+00:00
-- url     : https://prove2.me/submissions/30b2d509-5ff5-417c-b076-d2e8f2377680

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
namespace Snapshot
theorem _root_.solution {lim : Limits} {N out bankValues caps cut : ℕ}
    {f g : Config} {μ ν : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G)
    (H : ∀ x<cut, ν x=μ x)
    (hcodes : f.bank+f.nb≤cut) (hF : f.bv+f.nb≤cut) (hG : g.bv+f.nb≤cut)
    (hH : bankValues+(N+1)*f.nb≤cut) : Snapshot lim out bankValues caps f g ν Q E F G := by
  refine { S with bankRead:=?_,Fbank:=?_,Gbank:=?_,Hbank:=?_ }
  · intro j hj; rw [H _ (by omega)]; exact S.bankRead j hj
  · intro j hj; rw [H _ (by omega)]; exact S.Fbank j hj
  · intro j hj; rw [H _ (by omega)]; exact S.Gbank j hj
  · intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb hk
    have hs : (N+1)*f.nb=N*f.nb+f.nb := by ring
    rw [H _ (by omega)]
    exact S.Hbank k hk j hj
end Snapshot
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState
