-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalEuler.positive_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:03:41.886101+00:00
-- url     : https://prove2.me/submissions/1e70ce09-5882-4285-8ecd-38ccdaba98f0

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_ordinal_spec
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_physical_bank
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_physical_near
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_bank
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_near

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalEuler
theorem _root_.solution {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<rank (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i)
    (i : Fin N) (hi : 0<(R i).val) :
    physicalWord bankWords nearWords bv nv (rowKey R bankWords nearWords nb nn T bv nv i.val)=
      predecessor R i := by
  by_cases hr : rank (predecessor R i)≤T
  · rw [rowKey_bank R bankWords nearWords i hi hr]
    obtain ⟨hj,he⟩ := ordinal_spec (hbank _ hr)
    rw [physical_bank bankWords nearWords hsep hj,he]
  · rw [rowKey_near R bankWords nearWords i hi (by omega)]
    rw [physical_near]
    exact (ordinal_spec (hnear i (by omega))).2
end ThreeSum.TernaryPhysicalEuler
