-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalEuler.rowKey_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:23.523531+00:00
-- url     : https://prove2.me/submissions/e7898b3a-e930-4b53-9495-a7bd56eef3f2

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_precedes

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalEuler
theorem _root_.solution {N nb nn T bv nv : ℕ} (Q R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv) (hnb : 0<nb)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) :
    rowKey R bankWords nearWords nb nn T bv nv i.val<nv+nn := by
  rcases rowKey_precedes Q R bankWords nearWords hsep hnb hbank hnear hRQ i with hb | ⟨j,hj,he,_⟩
  · omega
  · omega
end ThreeSum.TernaryPhysicalEuler
