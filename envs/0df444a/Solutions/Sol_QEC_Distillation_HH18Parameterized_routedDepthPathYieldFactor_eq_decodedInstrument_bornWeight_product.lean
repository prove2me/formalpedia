-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_eq_decodedInstrument_bornWeight_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:56:06.531201+00:00
-- url     : https://prove2.me/submissions/d9b0b156-ddba-4728-a9f0-de26d4478f38

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathYieldFactor_eq_actualStageSuccessProduct


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
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) =
      ∏ stage : Fin depth,
        (decodedInstrument h hdegree).bornWeight .accepted
          (prepareMeasuredResources m w
            (noisyResources m w
              (routedDepthPathRate h hdegree epsilon hsmall stage.1
                (routedDepthPathStagePath m w depth path stage)))) := by
  rw [routedDepthPathYieldFactor_eq_actualStageSuccessProduct]
  apply Finset.prod_congr rfl
  intro stage _
  exact routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
    h hdegree epsilon hsmall depth path stage
end QEC.Distillation.HH18Parameterized
