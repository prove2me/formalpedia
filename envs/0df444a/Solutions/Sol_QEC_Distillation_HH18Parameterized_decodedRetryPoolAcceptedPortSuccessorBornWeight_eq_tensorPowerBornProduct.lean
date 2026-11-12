-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:17:43.152212+00:00
-- url     : https://prove2.me/submissions/dd48a6da-0639-4a03-b6af-ab6af3dcb53e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortSuccessorInputChannel_mapDensity
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_bornWeight_tensorPowerProductInput


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)) :
    decodedRetryPoolAcceptedPortSuccessorBornWeight
        h hdegree epsilon z q stage hstage port hhalf rhoUnit history =
      tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) history := by
  rw [decodedRetryPoolAcceptedPortSuccessorBornWeight,
    decodedRetryPoolAcceptedPortSuccessorInputChannel_mapDensity
      h hdegree epsilon z q stage hstage port hhalf rhoUnit]
  exact decodedRetryPoolInstrument_bornWeight_tensorPowerProductInput
    h hdegree
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)
    (decodedRetryPoolBackwardSchedule m w z q
      ⟨stage.1 + 1, hstage⟩)
    (noisyResources m w
      (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf))
    rhoUnit history
end QEC.Distillation.HH18Parameterized
