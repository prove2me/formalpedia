-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughGlobalOperator_eq_routed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:10:07.243679+00:00
-- url     : https://prove2.me/submissions/e7bee8ec-0bab-4d6f-8433-596e92e731ee

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_EnoughBranchSum
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Branches_ChannelFirstFilteredBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
import Theorems.Thm_QEC_Semantics_FiniteInstrument_toFiniteInstrument_bindDependent_branchOperator_filter_sum_eq


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
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorStageSelectedEnoughGlobalOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
        h hdegree epsilon z q stage hstage port rhoUnit := by
  unfold decodedRetryPoolSuccessorStageSelectedEnoughGlobalOperator
    decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
    decodedRetryPoolSuccessorStageSelectedPoolEnough
    decodedRetryPoolSuccessorStageJointInput
    decodedRetryPoolSuccessorStageInstrument
  exact toFiniteInstrument_bindDependent_branchOperator_filter_sum_eq
    (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage)
    ((decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩)).tensorPower (logicalOutputCount m w))
    (fun history => decodedRetryPoolOutcomeEnough
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
      (tensorPowerHistoryAt _ (logicalOutputCount m w) history
        (decodedRetryPoolLogicalSiteFinEquiv m w port)) = true)
    (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
      (decodedRetryPoolBackwardSchedule m w z q stage)).toOperator
end QEC.Distillation.HH18Parameterized
