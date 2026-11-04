-- Prove2me | solution 1 for ThreeSum.LightWeightedPreparedState.Snapshot.transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:46:51.903723+00:00
-- url     : https://prove2.me/submissions/bcb98927-0c01-4b7b-97b9-38cea99bd49b

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
end ThreeSum.LightWeightedPreparedState
