-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSelectedPortChannel_mapDensity_acceptedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:40:28.955804+00:00
-- url     : https://prove2.me/submissions/81da32a0-786e-43f6-8fbd-1154174d0504

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    (decodedRetryPoolSelectedPortChannel m w port).mapDensity
        (resourceDecodedRun h hdegree
          (noisyResources m w epsilon)).acceptedOutput =
      selectedLogicalPortTransportedAcceptedOutput
        h hdegree epsilon port := by
  rfl
end QEC.Distillation.HH18Parameterized
