-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.decodedErrorBranch_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:26:20.288206+00:00
-- url     : https://prove2.me/submissions/406cd703-57e9-46b9-bbef-224342c7d2f4

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
import Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchDensity_to_errorBranchOperator
import Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchState_normSq


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
theorem _root_.solution (error : PhysicalErrorWord) :
    (decodedErrorBranch error).toOperator =
      decoderChannel (HH18SyndromeDecoding.errorBranchOperator error) := by
  change decoderChannel
      (DensityOperator.pureDensity (errorBranchState error)
        (errorBranchState_normSq error)).toOperator = _
  rw [errorBranchDensity_to_errorBranchOperator]
end QEC.Distillation.HH18Protocol
