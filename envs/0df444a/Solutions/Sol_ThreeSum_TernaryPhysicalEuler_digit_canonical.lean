-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalEuler.digit_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:26.566308+00:00
-- url     : https://prove2.me/submissions/39998cc8-11a9-40d6-985a-593e88e5fc32

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalEuler
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) :
    LightTernaryPredecessor.digit N (LightTernaryEulerMetadata.lowAt N i.val)
      (LightTernaryEulerMetadata.highAt N i.val) (address R)=(R i).val := by
  exact digit_eq R i
end ThreeSum.TernaryPhysicalEuler
