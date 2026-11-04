-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalEuler.near_predecessor_present
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:14.062206+00:00
-- url     : https://prove2.me/submissions/c3d70bb9-664e-4c2e-a743-62daa2b49ea6

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Theorems.Thm_ThreeSum_TernaryEuler_predecessor_below


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalEuler
theorem _root_.solution {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) (hr : T<rank (predecessor R i)) :
    ∃ j<nn, nearWords j=predecessor R i := by
  exact hnear _ (fun k => (predecessor_below R i k).trans (hRQ k)) hr
end ThreeSum.TernaryPhysicalEuler
