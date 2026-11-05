-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.near_predecessor_present
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:12:48.357524+00:00
-- url     : https://prove2.me/submissions/d6f72530-b501-4d2e-b8d1-2dfdd2ffb2a7

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PhysicalEuler
import Theorems.Thm_ThreeSum_TernaryEuler_predecessor_below
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_predecessor_below


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
theorem _root_.solution {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<cacheCost W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) (hr : T<cacheCost (predecessor R i)) :
    ∃ j<nn, nearWords j=predecessor R i := by
  exact hnear _ (fun k => (predecessor_below R i k).trans (hRQ k)) hr
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
