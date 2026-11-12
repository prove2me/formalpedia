-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.acceptedOutputTraceError_le_two_mul_residualCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:45:51.982241+00:00
-- url     : https://prove2.me/submissions/1c9a5d7b-8600-4d50-8365-2a0d432cf322

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedOutputTraceError_le_two_mul_acceptedResidual
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedResidualError_le_residualCoefficient


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
      (idealLogicalTOutput m w) ≤
        2 * residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by
  calc
    outputTraceError
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
        (idealLogicalTOutput m w) ≤ 2 * acceptedResidualError h hdegree epsilon :=
      acceptedOutputTraceError_le_two_mul_acceptedResidual h hdegree epsilon
    _ ≤ 2 * (residualCoefficient w r m * epsilon.1 ^ codeDistance r w) := by
      exact mul_le_mul_of_nonneg_left
        (acceptedResidualError_le_residualCoefficient h hdegree epsilon) (by norm_num)
    _ = 2 * residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by ring
end QEC.Distillation.HH18Parameterized
