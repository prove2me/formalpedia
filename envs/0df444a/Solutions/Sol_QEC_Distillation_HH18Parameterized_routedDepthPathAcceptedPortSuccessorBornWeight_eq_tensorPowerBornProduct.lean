-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:03:13.048267+00:00
-- url     : https://prove2.me/submissions/169f5fe8-61e0-41eb-a588-7961c37d3e36

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_append_eq_nextInputRate


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
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)) :
    decodedRetryPoolAcceptedPortSuccessorBornWeight h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall depth path)
        z q stage hstage port
        (routedDepthPathNextHalf h hdegree epsilon hsmall path port)
        rhoUnit history =
      tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w
          (noisyResources m w
            (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
              (routedDepthOutputPathAppend m w depth path port))))
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) history := by
  rw [routedDepthPathRate_append_eq_nextInputRate]
  exact
    decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
      h hdegree
      (routedDepthPathRate h hdegree epsilon hsmall depth path)
      z q stage hstage port
      (routedDepthPathNextHalf h hdegree epsilon hsmall path port)
      rhoUnit history
end QEC.Distillation.HH18Parameterized
