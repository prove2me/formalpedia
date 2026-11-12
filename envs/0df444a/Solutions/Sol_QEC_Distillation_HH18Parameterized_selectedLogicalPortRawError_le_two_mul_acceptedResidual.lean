-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.selectedLogicalPortRawError_le_two_mul_acceptedResidual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:25:38.095713+00:00
-- url     : https://prove2.me/submissions/c3cce0df-3875-471d-b9db-1ee633931b15

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortRawError_le_outputTrace
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedOutputTraceError_le_two_mul_acceptedResidual


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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree epsilon port ≤
      2 * acceptedResidualError h hdegree epsilon := by
  calc
    selectedLogicalPortRawError h hdegree epsilon port ≤
        outputTraceError
          (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
          (idealLogicalTOutput m w) :=
      selectedLogicalPortRawError_le_outputTrace h hdegree epsilon port
    _ ≤ 2 * acceptedResidualError h hdegree epsilon :=
      acceptedOutputTraceError_le_two_mul_acceptedResidual h hdegree epsilon
end QEC.Distillation.HH18Parameterized
