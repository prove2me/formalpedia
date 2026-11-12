-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.decoderChannel_zeroErrorBranch_eq_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:25:49.981438+00:00
-- url     : https://prove2.me/submissions/bf86a682-20a8-42ff-b5ae-b64f5514343f

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_one
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_hh18PhysicalTInvBranch_eq_logicalT
import Theorems.Thm_QEC_Distillation_HH18Protocol_decoderChannel_rankOne_encoded


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instDecodedBridgeClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instDecodedBridgeClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution :
    decoderChannel
        (HH18SyndromeDecoding.errorBranchOperator (0 : PhysicalErrorWord)) =
      idealLogicalTOutput.toOperator := by
  change decoderChannel
      (InnerProductSpace.rankOne Complex
        (HH18NoisyInput.hh18PhysicalTInvErrorBranch (0 : PhysicalErrorWord))
        (HH18NoisyInput.hh18PhysicalTInvErrorBranch (0 : PhysicalErrorWord))).toLinearMap = _
  have hbranch :
      HH18NoisyInput.hh18PhysicalTInvErrorBranch (0 : PhysicalErrorWord) =
        ambientEncodingIsometry idealLogicalTOutputState := by
    rw [HH18NoisyInput.hh18PhysicalTInvErrorBranch,
      HH18NoisyInput.zErrorOperator]
    change PauliSymplectic.toQubitOperator (PauliSymplectic.binaryOne (ι := PhysicalSite))
        HH18NoisyInput.hh18PhysicalTInvBranch = _
    rw [PauliSymplectic.toQubitOperator_one]
    change HH18NoisyInput.hh18PhysicalTInvBranch =
      HH18NoisyInput.hh18_15_1_0_encodedCode.encode
        (HH18PuncturedReedMuller.logicalT 0 4 HH18NoisyInput.hh18LogicalPlusInput)
    exact HH18NoisyInput.hh18PhysicalTInvBranch_eq_logicalT
  rw [hbranch, decoderChannel_rankOne_encoded]
  rfl
end QEC.Distillation.HH18Protocol
