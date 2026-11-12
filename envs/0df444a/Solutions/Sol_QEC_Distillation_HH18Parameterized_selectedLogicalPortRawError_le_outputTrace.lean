-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.selectedLogicalPortRawError_le_outputTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:21:11.98013+00:00
-- url     : https://prove2.me/submissions/4d6d1ff1-cca1-4fb4-8e20-27e4fdaeecd1

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortTransportedAcceptedOutput_traceDistance_le_outputTrace
import Theorems.Thm_QEC_Distillation_OneQubitABasisSupport_negativeABornWeight_le_traceDistance_to_aZero


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
      outputTraceError
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
        (idealLogicalTOutput m w) := by
  unfold selectedLogicalPortRawError
  calc
    aBasisInstrument.bornWeight .negative
        (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port) ≤
        traceNorm
          ((selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port).toOperator -
            aZeroDensity.toOperator) :=
      OneQubitABasisSupport.negativeABornWeight_le_traceDistance_to_aZero _
    _ ≤ outputTraceError
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
        (idealLogicalTOutput m w) :=
      selectedLogicalPortTransportedAcceptedOutput_traceDistance_le_outputTrace
        h hdegree epsilon port
end QEC.Distillation.HH18Parameterized
