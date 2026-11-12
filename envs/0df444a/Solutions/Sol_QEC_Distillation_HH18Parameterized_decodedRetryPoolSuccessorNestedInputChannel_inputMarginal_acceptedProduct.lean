-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_inputMarginal_acceptedProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:34:45.352229+00:00
-- url     : https://prove2.me/submissions/6741aa55-4b80-425b-895a-2f0ea3b37d90

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorNestedInputChannel_inputMarginal
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRoutedBranchChannel_mapDensity_recordPreparation_acceptedProduct

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
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    tensorPowerInputMarginal (logicalOutputCount m w)
        ((decodedRetryPoolSuccessorNestedInputChannel
          m w z q stage hstage).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage)))
        (decodedRetryPoolLogicalSiteFinEquiv m w port) =
      tensorPowerProductInput
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) := by
  rw [decodedRetryPoolSuccessorNestedInputChannel_inputMarginal]
  exact
    decodedRetryPoolSuccessorRoutedBranchChannel_mapDensity_recordPreparation_acceptedProduct
      h hdegree epsilon z q stage hstage port hhalf rhoUnit
end QEC.Distillation.HH18Parameterized
