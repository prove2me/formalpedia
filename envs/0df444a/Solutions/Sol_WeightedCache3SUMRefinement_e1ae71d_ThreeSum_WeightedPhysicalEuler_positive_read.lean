-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.positive_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:23:07.54726+00:00
-- url     : https://prove2.me/submissions/a6a3eceb-c602-4355-9723-c522b3551173

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PhysicalEuler
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_ordinal_spec
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_physical_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_physical_near
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_rowKey_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_rowKey_near

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
theorem _root_.solution {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv)
    (hbank : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<cacheCost (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i)
    (i : Fin N) (hi : 0<(R i).val) :
    physicalWord bankWords nearWords bv nv (rowKey R bankWords nearWords nb nn T bv nv i.val)=
      predecessor R i := by
  by_cases hr : cacheCost (predecessor R i)≤T
  · rw [rowKey_bank R bankWords nearWords i hi hr]
    obtain ⟨hj,he⟩ := ordinal_spec (hbank _ hr)
    rw [physical_bank bankWords nearWords hsep hj,he]
  · rw [rowKey_near R bankWords nearWords i hi (by omega)]
    rw [physical_near]
    exact (ordinal_spec (hnear i (by omega))).2
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
