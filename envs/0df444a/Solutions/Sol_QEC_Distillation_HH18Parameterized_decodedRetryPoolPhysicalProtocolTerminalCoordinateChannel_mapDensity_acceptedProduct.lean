-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel_mapDensity_acceptedProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:23:59.4635+00:00
-- url     : https://prove2.me/submissions/aa14bd84-9e45-42c0-aca7-d4bb2d7bcf0f

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedProductCoordinateChannel_mapDensity

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
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    (decodedRetryPoolAcceptedProductCoordinateChannel m w
      (decodedRetryPoolBackwardSchedule m w z q
        (decodedRetryPoolProtocolTerminalStage z hz))
      coordinate.2.1 coordinate.2.2).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            (decodedRetryPoolProtocolTerminalStage z hz))) =
      selectedLogicalPortTransportedAcceptedOutput
        h hdegree epsilon coordinate.2.2 :=
  decodedRetryPoolAcceptedProductCoordinateChannel_mapDensity
    h hdegree epsilon rhoUnit _ coordinate.2.1 coordinate.2.2
end QEC.Distillation.HH18Parameterized
