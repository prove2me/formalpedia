-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleActualOutputError_exists_path_with_decodedInstrument_weights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:04:19.965431+00:00
-- url     : https://prove2.me/submissions/9e5809e2-98be-4b88-9be3-ef9aa1f85750

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleActualOutputError_exists_path


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
    (depth : Nat) :
    ∃ path : routedDepthOutputSlots m w depth,
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth =
          (routedDepthPathRate h hdegree epsilon hsmall depth path).1 ∧
        ∀ stage : Fin depth,
          (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability =
            (decodedInstrument h hdegree).bornWeight .accepted
              (prepareMeasuredResources m w
                (noisyResources m w
                  (routedDepthPathRate h hdegree epsilon hsmall stage.1
                    (routedDepthPathStagePath m w depth path stage)))) := by
  obtain ⟨path, hpath⟩ :=
    routedDepthScheduleActualOutputError_exists_path h hdegree epsilon hsmall depth
  refine ⟨path, hpath, ?_⟩
  intro stage
  exact routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
    h hdegree epsilon hsmall depth path stage
end QEC.Distillation.HH18Parameterized
