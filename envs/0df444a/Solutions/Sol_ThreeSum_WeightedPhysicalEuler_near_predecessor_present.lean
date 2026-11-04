-- Prove2me | solution 1 for ThreeSum.WeightedPhysicalEuler.near_predecessor_present
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:01:00.91926+00:00
-- url     : https://prove2.me/submissions/67b1fcb0-777c-4f8b-9480-23e7b46bf68d

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler
import Theorems.Thm_ThreeSum_TernaryEuler_predecessor_below
import Theorems.Thm_WeightedCache_predecessor_below


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedPhysicalEuler
theorem _root_.solution {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<cacheCost W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) (hr : T<cacheCost (predecessor R i)) :
    ∃ j<nn, nearWords j=predecessor R i := by
  exact hnear _ (fun k => (predecessor_below R i k).trans (hRQ k)) hr
end ThreeSum.WeightedPhysicalEuler
