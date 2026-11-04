-- Prove2me | solution 1 for ThreeSum.WeightedPhysicalEuler.digit_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:25.126265+00:00
-- url     : https://prove2.me/submissions/a2558a41-b090-46ac-9012-147e0173ff0c

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedPhysicalEuler
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) :
    LightWeightedPredecessor.digit N (LightWeightedEulerMetadata.lowAt N i.val)
      (LightWeightedEulerMetadata.highAt N i.val) (address R)=(R i).val := by
  exact digit_eq R i
end ThreeSum.WeightedPhysicalEuler
