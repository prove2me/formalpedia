-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedInstrument_branchOperator_prepareMeasuredResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:23:16.430477+00:00
-- url     : https://prove2.me/submissions/01f46a55-c31e-4bb0-aa0e-8598e4f1d453

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_branchOperator_eq_decodedRawInstrument
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRawInstrument_branchOperator_eq_decoder
import Theorems.Thm_QEC_Distillation_HH18Parameterized_resourcePostselectionInstrument_branchOperator


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
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) :
    (decodedInstrument h hdegree).branchOperator outcome
        (prepareMeasuredResources m w inputs).toOperator =
      (endpointWeight h hdegree inputs outcome : Complex) •
        ((resourceDecodedRun h hdegree inputs).conditionalOutput outcome).toOperator := by
  rw [decodedInstrument_branchOperator_eq_decodedRawInstrument,
    decodedRawInstrument_branchOperator_eq_decoder,
    resourcePostselectionInstrument_branchOperator]
  change decoderChannel h (rawEndpoint h hdegree inputs outcome) = _
  calc
    decoderChannel h (rawEndpoint h hdegree inputs outcome) =
        decoderChannel h
          ((endpointWeight h hdegree inputs outcome : Complex) •
            (endpointCompletion h hdegree inputs outcome).toOperator) := by
          rw [endpointWeight_smul_completion_toOperator]
    _ = (endpointWeight h hdegree inputs outcome : Complex) •
        decoderChannel h
          (endpointCompletion h hdegree inputs outcome).toOperator := by
          exact map_smul (decoderChannel h).toLinearMap _ _
    _ = _ := by
      cases outcome <;> rfl
end QEC.Distillation.HH18Parameterized
