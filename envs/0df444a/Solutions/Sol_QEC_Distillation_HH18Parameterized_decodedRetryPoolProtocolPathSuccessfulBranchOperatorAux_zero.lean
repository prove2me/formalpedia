-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:09:45.085691+00:00
-- url     : https://prove2.me/submissions/4ac7e698-ea0b-46bf-83c7-a92cf06abe8c

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
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) (path : routedDepthOutputSlots m w 0) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
        h hdegree z q hz rho 0 hz path =
      decodedRetryPoolProtocolRootSuccessfulBranchOperator
        h hdegree z q hz rho :=
  rfl
end QEC.Distillation.HH18Parameterized
