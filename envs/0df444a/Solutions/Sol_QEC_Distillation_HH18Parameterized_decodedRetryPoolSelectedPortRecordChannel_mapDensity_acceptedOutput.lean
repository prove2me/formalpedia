-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSelectedPortRecordChannel_mapDensity_acceptedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:48:14.499138+00:00
-- url     : https://prove2.me/submissions/676888aa-fe21-49ec-83d8-bea43a1de303

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSelectedPortChannel_mapDensity_acceptedOutput
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorOneQubitRecordChannel_selectedOutput


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
    (decodedRetryPoolSelectedPortRecordChannel m w port).mapDensity
        (resourceDecodedRun h hdegree
          (noisyResources m w epsilon)).acceptedOutput =
      decodedRetryPoolOneQubitRecordDensity
        (selectedLogicalPortRawParameter h hdegree epsilon port) := by
  rw [decodedRetryPoolSelectedPortRecordChannel,
    QuantumChannel.comp_mapDensity,
    decodedRetryPoolSelectedPortChannel_mapDensity_acceptedOutput]
  exact decodedRetryPoolSuccessorOneQubitRecordChannel_selectedOutput
    h hdegree epsilon port
end QEC.Distillation.HH18Parameterized
