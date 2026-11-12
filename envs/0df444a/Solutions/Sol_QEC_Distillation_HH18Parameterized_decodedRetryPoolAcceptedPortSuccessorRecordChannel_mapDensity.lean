-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortSuccessorRecordChannel_mapDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:01:23.269065+00:00
-- url     : https://prove2.me/submissions/e2bfe4be-1288-4ad3-b3e0-3ce7f41a5cab

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortRecordRegisterChannel_mapDensity

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
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    (decodedRetryPoolAcceptedPortSuccessorRecordChannel
      m w z q stage hstage port).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      decodedRetryPoolSuccessorPortRecordProductDensity
        m w z q stage hstage
        (selectedLogicalPortRawParameter h hdegree epsilon port) rhoUnit := by
  rw [decodedRetryPoolAcceptedPortSuccessorRecordChannel,
    QuantumChannel.comp_mapDensity,
    decodedRetryPoolAcceptedPortRecordRegisterChannel_mapDensity
      h hdegree epsilon rhoUnit port
        (decodedRetryPoolBackwardSchedule m w z q stage)]
  rfl
end QEC.Distillation.HH18Parameterized
