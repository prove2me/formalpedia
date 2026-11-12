-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18NextInputRawError_le_cubic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:17:46.50083+00:00
-- url     : https://prove2.me/submissions/974e7cd1-887d-47fe-b3dd-2798f86505c5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18NextInputRawError_le_outputTrace
import Theorems.Thm_QEC_Distillation_HH18Protocol_acceptedOutputTraceError_le_two_mul_acceptedResidual
import Theorems.Thm_QEC_Distillation_HH18Protocol_acceptedResidualError_le_cubic


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18NextInputRawError epsilon ≤
      (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by
  calc
    hh18NextInputRawError epsilon ≤
        hh18OutputTraceError
          (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
          idealLogicalTOutput := hh18NextInputRawError_le_outputTrace epsilon
    _ ≤ 2 * acceptedResidualError epsilon :=
      acceptedOutputTraceError_le_two_mul_acceptedResidual epsilon
    _ ≤ 2 * (residualCubicCoefficient * epsilon.1 ^ 3) := by
      exact mul_le_mul_of_nonneg_left (acceptedResidualError_le_cubic epsilon) (by norm_num)
    _ = (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by ring
end QEC.Distillation.HH18Protocol
