-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.acceptedOutputTraceError_le_two_mul_acceptedResidual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:13:32.74997+00:00
-- url     : https://prove2.me/submissions/50743326-5888-4aa2-b712-6ca932484fc5

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
import Theorems.Thm_QEC_Distillation_HH18Protocol_traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass
import Theorems.Thm_QEC_Distillation_HH18Protocol_decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
import Theorems.Thm_QEC_Distillation_FiniteDecodedTrace_normalized_residual_traceNorm_le
import Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeight_accepted_eq_rawSuccessMass
import Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeight_accepted_pos
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_pos
import Theorems.Thm_QEC_Distillation_HH18Protocol_resourceDecodedRun_acceptedOutput


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
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18OutputTraceError
      (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
      idealLogicalTOutput ≤ 2 * acceptedResidualError epsilon := by
  have hsuccess : 0 < endpointWeight (noisyResources epsilon) .accepted :=
    endpointWeight_accepted_pos epsilon
  rw [resourceDecodedRun_acceptedOutput (noisyResources epsilon) hsuccess]
  unfold hh18OutputTraceError
  rw [QuantumChannel.mapDensity_toOperator, endpointConditional_toOperator, map_smul]
  rw [endpointWeight_accepted_eq_rawSuccessMass]
  have hrewrite :
      ((rawSuccessMass epsilon : Complex)⁻¹) •
          decoderChannel (rawEndpoint (noisyResources epsilon) .accepted) -
        idealLogicalTOutput.toOperator =
      (rawSuccessMass epsilon : Complex)⁻¹ •
        acceptedResidualDecodedDifference epsilon := by
    rw [← decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual epsilon]
    have hne : (rawSuccessMass epsilon : Complex) ≠ 0 := by
      exact_mod_cast (ne_of_gt (rawSuccessMass_pos epsilon))
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hrewrite]
  have hmass := traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass epsilon
  have hsuccessReal : 0 < rawSuccessMass epsilon := rawSuccessMass_pos epsilon
  have hnormalized := FiniteDecodedTrace.normalized_residual_traceNorm_le
    (rawSuccessMass epsilon) (rawAcceptedResidualErrorMass epsilon)
    (acceptedResidualDecodedDifference epsilon) hsuccessReal hmass
  have hratio :
      2 * (rawAcceptedResidualErrorMass epsilon / rawSuccessMass epsilon) =
        2 * acceptedResidualError epsilon := by
      unfold acceptedResidualError
      field_simp [ne_of_gt hsuccessReal]
  rwa [hratio] at hnormalized
end QEC.Distillation.HH18Protocol
