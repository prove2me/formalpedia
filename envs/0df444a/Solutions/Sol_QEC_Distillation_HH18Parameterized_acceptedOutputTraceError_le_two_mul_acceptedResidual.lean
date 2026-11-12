-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.acceptedOutputTraceError_le_two_mul_acceptedResidual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:22:12.964724+00:00
-- url     : https://prove2.me/submissions/e5b8950e-64b1-453c-8e32-66dbb5aae9bc

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
import Theorems.Thm_QEC_Distillation_FiniteDecodedTrace_normalized_residual_traceNorm_le
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_eq_acceptedBernoulliMass
import Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_resourceDecodedRun_acceptedOutput_noisyResources


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    outputTraceError
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
      (idealLogicalTOutput m w) ≤ 2 * acceptedResidualError h hdegree epsilon := by
  have hsuccess : 0 < endpointWeight h hdegree (noisyResources m w epsilon) .accepted :=
    endpointWeight_accepted_pos h hdegree epsilon
  rw [resourceDecodedRun_acceptedOutput_noisyResources h hdegree epsilon]
  unfold outputTraceError
  rw [QuantumChannel.mapDensity_toOperator, endpointConditional_toOperator, map_smul]
  rw [endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon]
  have hrewrite :
      ((acceptedBernoulliMass w r m epsilon : Complex)⁻¹) •
          decoderChannel h (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted) -
        (idealLogicalTOutput m w).toOperator =
      (acceptedBernoulliMass w r m epsilon : Complex)⁻¹ •
        acceptedResidualDecodedDifference h hdegree epsilon := by
    rw [← decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual h hdegree epsilon]
    have hne : (acceptedBernoulliMass w r m epsilon : Complex) ≠ 0 := by
      exact_mod_cast (ne_of_gt (acceptedBernoulliMass_pos h epsilon))
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hrewrite]
  have hmass :=
    traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass h hdegree epsilon
  have hsuccessReal : 0 < acceptedBernoulliMass w r m epsilon :=
    acceptedBernoulliMass_pos h epsilon
  have hnormalized := FiniteDecodedTrace.normalized_residual_traceNorm_le
    (acceptedBernoulliMass w r m epsilon) (rawAcceptedResidualErrorMass w r m epsilon)
    (acceptedResidualDecodedDifference h hdegree epsilon) hsuccessReal hmass
  have hratio :
      2 * (rawAcceptedResidualErrorMass w r m epsilon /
        acceptedBernoulliMass w r m epsilon) =
        2 * acceptedResidualError h hdegree epsilon := by
    unfold acceptedResidualError
    rw [endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon]
  rwa [hratio] at hnormalized
end QEC.Distillation.HH18Parameterized
