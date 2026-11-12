-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortRecordRegisterChannel_mapDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:57:23.236478+00:00
-- url     : https://prove2.me/submissions/a26fbc85-21e0-4bda-b0b4-f355797a2cb8

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortRecordProductChannel_mapDensity


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
    (port : LogicalSite m w) (required : Nat) :
    (decodedRetryPoolAcceptedPortRecordRegisterChannel
      m w port required).mapDensity
        (decodedRetryPoolAcceptedProductDensity
          h hdegree epsilon rhoUnit required) =
      decodedRetryPoolAcceptedPortRecordRegisterProductDensity
        m w (selectedLogicalPortRawParameter h hdegree epsilon port)
        rhoUnit required := by
  rw [decodedRetryPoolAcceptedPortRecordRegisterChannel,
    QuantumChannel.comp_mapDensity,
    decodedRetryPoolAcceptedPortRecordProductChannel_mapDensity
      h hdegree epsilon rhoUnit port required]
  rfl
end QEC.Distillation.HH18Parameterized
