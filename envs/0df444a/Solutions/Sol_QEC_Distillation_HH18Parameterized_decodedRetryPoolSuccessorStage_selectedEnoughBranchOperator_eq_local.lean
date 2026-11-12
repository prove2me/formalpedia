-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:21:01.53064+00:00
-- url     : https://prove2.me/submissions/fcd51ddb-65d3-4100-bf14-961cebc976d7

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_EnoughBranchSum
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Branches_ChannelFirstFilteredBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_coordinateOperator_branchOperator_filter_sum_eq


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
    decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      decodedRetryPoolSuccessorStageLocalEnoughOperator h hdegree z q stage hstage
        (tensorPowerCoordinateOperator (logicalOutputCount m w)
          (decodedRetryPoolLogicalSiteFinEquiv m w port)
          (decodedRetryPoolSuccessorStageJointInput
            h hdegree epsilon z q stage hstage rhoUnit).toOperator) := by
  rw [decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq]
  unfold decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
    decodedRetryPoolSuccessorStageLocalEnoughOperator
  exact tensorPower_coordinateOperator_branchOperator_filter_sum_eq
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
    (decodedRetryPoolInstrument_complete h hdegree
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
    (fun outcome => decodedRetryPoolOutcomeEnough
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
      outcome = true)
    (logicalOutputCount m w)
    (decodedRetryPoolSuccessorStageJointInput
      h hdegree epsilon z q stage hstage rhoUnit).toOperator
    (decodedRetryPoolLogicalSiteFinEquiv m w port)
end QEC.Distillation.HH18Parameterized
