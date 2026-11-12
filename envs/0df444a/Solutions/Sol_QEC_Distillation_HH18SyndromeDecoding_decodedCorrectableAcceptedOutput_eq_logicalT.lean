-- Prove2me | solution 1 for QEC.Distillation.HH18SyndromeDecoding.decodedCorrectableAcceptedOutput_eq_logicalT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:28:18.937207+00:00
-- url     : https://prove2.me/submissions/3ef87ec4-6351-4007-afb5-bd56d3a4b991

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_hh18PhysicalTInvBranch_eq_logicalT


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SyndromeDecoding
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.HH18SyndromeDecoding
theorem _root_.solution
    (error : PhysicalErrorWord) (hweight : HammingWeight error ≤ 1)
    (haccept : Accepts error) :
    decodedCorrectableAcceptedOutput error hweight haccept =
      HH18PuncturedReedMuller.logicalT 0 4
        HH18NoisyInput.hh18LogicalPlusInput := by
  unfold decodedCorrectableAcceptedOutput
  apply HH18NoisyInput.hh18_15_1_0_encodedCode.encoding.injective
  rw [HH18NoisyInput.hh18_15_1_0_encodedCode.encoding.apply_symm_apply]
  apply Subtype.ext
  change HH18NoisyInput.hh18PhysicalTInvErrorBranch error =
    HH18NoisyInput.hh18_15_1_0_encodedCode.encode
      (HH18PuncturedReedMuller.logicalT 0 4
        HH18NoisyInput.hh18LogicalPlusInput)
  rw [correctableAcceptedError_eq_zero error hweight haccept,
    zeroErrorBranch_eq_ideal,
    HH18NoisyInput.hh18PhysicalTInvBranch_eq_logicalT]
end QEC.Distillation.HH18SyndromeDecoding
