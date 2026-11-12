-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:15:11.069841+00:00
-- url     : https://prove2.me/submissions/c61c6b79-899e-4c82-98da-01fe9e357cd4

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_bornWeight_prepareMeasuredResources
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathActualRun_eq_resourceDecodedRun


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability =
      (decodedInstrument h hdegree).bornWeight .accepted
        (prepareMeasuredResources m w
          (noisyResources m w
            (routedDepthPathRate h hdegree epsilon hsmall stage.1
              (routedDepthPathStagePath m w depth path stage)))) := by
  unfold routedDepthPathStageRun
  rw [routedDepthPathActualRun_eq_resourceDecodedRun]
  change endpointWeight h hdegree
      (noisyResources m w
        (routedDepthPathRate h hdegree epsilon hsmall stage.1
          (routedDepthPathStagePath m w depth path stage))) .accepted = _
  rw [decodedInstrument_bornWeight_prepareMeasuredResources]
end QEC.Distillation.HH18Parameterized
