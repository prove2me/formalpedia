-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathEnoughMassAux_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:10:10.951285+00:00
-- url     : https://prove2.me/submissions/19efb6ac-345a-44bc-9772-61e06892b2fb

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator

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
    (z q stage : Nat) (hstage : stage + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (path : routedDepthOutputSlots m w (stage + 1)) :
    decodedRetryPoolProtocolPathEnoughMassAux
        h hdegree epsilon hsmall z q rhoUnit (stage + 1) hstage path =
      decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage (by omega)
            (routedDepthOutputPathInit m w stage path) *
        decodedRetryPoolEnoughMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage
              (routedDepthOutputPathInit m w stage path))
            z q ⟨stage, by omega⟩ hstage
            (routedDepthOutputPathLast m w stage path)
            (routedDepthPathNextHalf h hdegree epsilon hsmall
              (routedDepthOutputPathInit m w stage path)
              (routedDepthOutputPathLast m w stage path))
            rhoUnit) :=
  rfl
end QEC.Distillation.HH18Parameterized
