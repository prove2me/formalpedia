-- Prove2me | solution 1 for ThreeSum.WeightedPhysicalEuler.rowKey_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:38.701586+00:00
-- url     : https://prove2.me/submissions/b470651d-4e61-47f8-9786-df325d0df1cd

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler
import Theorems.Thm_ThreeSum_WeightedPhysicalEuler_rowKey_precedes

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedPhysicalEuler
theorem _root_.solution {N nb nn T bv nv : ℕ} (Q R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv) (hnb : 0<nb)
    (hbank : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ W, Below W Q → T<cacheCost W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) :
    rowKey R bankWords nearWords nb nn T bv nv i.val<nv+nn := by
  rcases rowKey_precedes Q R bankWords nearWords hsep hnb hbank hnear hRQ i with hb | ⟨j,hj,he,_⟩
  · omega
  · omega
end ThreeSum.WeightedPhysicalEuler
