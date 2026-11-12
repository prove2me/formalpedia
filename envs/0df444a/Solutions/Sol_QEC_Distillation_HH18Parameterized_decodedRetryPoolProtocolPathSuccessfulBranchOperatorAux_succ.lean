-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:10:31.900095+00:00
-- url     : https://prove2.me/submissions/119efbb0-bdce-43bb-861b-c57ba5af881d

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
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) (path : routedDepthOutputSlots m w (stage + 1)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
        h hdegree z q hz rho (stage + 1) hstage path =
      decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage
          (routedDepthOutputPathLast m w stage path)
          (decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
            h hdegree z q hz rho stage (by omega)
              (routedDepthOutputPathInit m w stage path)) :=
  rfl
end QEC.Distillation.HH18Parameterized
