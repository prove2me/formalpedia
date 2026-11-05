-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.digit_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:12:46.266048+00:00
-- url     : https://prove2.me/submissions/591b958b-837c-4acb-8157-3b40859d1715

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PhysicalEuler
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq


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
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) :
    LightWeightedPredecessor.digit N (LightWeightedEulerMetadata.lowAt N i.val)
      (LightWeightedEulerMetadata.highAt N i.val) (address R)=(R i).val := by
  exact digit_eq R i
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
