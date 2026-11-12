-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:16:08.105568+00:00
-- url     : https://prove2.me/submissions/25b5801b-a716-4d9c-8bf0-6126c4d502ad

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_EnoughBranchSum
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Branches_ChannelFirstFilteredBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStage_selectedEnoughGlobalOperator_eq_routed

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
      tensorPowerCoordinateOperator (logicalOutputCount m w)
        (decodedRetryPoolLogicalSiteFinEquiv m w port)
        (decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
          h hdegree epsilon z q stage hstage port rhoUnit) := by
  unfold decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
  rw [decodedRetryPoolSuccessorStage_selectedEnoughGlobalOperator_eq_routed]
end QEC.Distillation.HH18Parameterized
