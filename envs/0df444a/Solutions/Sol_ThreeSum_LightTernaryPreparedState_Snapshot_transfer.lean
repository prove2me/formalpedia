-- Prove2me | solution 1 for ThreeSum.LightTernaryPreparedState.Snapshot.transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:45:41.165236+00:00
-- url     : https://prove2.me/submissions/cfc7e65d-a75e-4d07-8173-8cc29a40c1aa

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
end ThreeSum.LightTernaryPreparedState
