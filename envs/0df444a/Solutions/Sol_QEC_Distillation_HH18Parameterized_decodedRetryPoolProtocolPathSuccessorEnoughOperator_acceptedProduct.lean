-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessorEnoughOperator_acceptedProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:49:14.461429+00:00
-- url     : https://prove2.me/submissions/5079c1df-289f-4298-81b0-e7db3f18130c

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStage_selectedEnoughBranch_sum


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
    (z q stage : Nat) (hstage : stage + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage port
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage, by omega⟩)).toOperator =
      (decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolSuccessorStageSelectedNextInput
          h hdegree epsilon z q ⟨stage, by omega⟩ hstage port hhalf
          rhoUnit) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree
          (selectedLogicalPortNextInputRate
            h hdegree epsilon port hhalf)
          rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)).toOperator := by
  exact decodedRetryPoolSuccessorStage_selectedEnoughBranch_sum
    h hdegree epsilon z q ⟨stage, by omega⟩ hstage port hhalf rhoUnit
end QEC.Distillation.HH18Parameterized
