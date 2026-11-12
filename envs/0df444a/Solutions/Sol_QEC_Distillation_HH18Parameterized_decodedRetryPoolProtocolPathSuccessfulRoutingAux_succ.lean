-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:06:01.27018+00:00
-- url     : https://prove2.me/submissions/515a7992-5075-41e9-b900-bdfc2f8af1dd

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z q stage : Nat) (hstage : stage + 1 < z)
    (path : routedDepthOutputSlots m w (stage + 1))
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q (stage + 1) hstage) :
    decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q (stage + 1) hstage path outcome =
      (decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q stage (by omega)
            (routedDepthOutputPathInit m w stage path) outcome.1 &&
        decodedRetryPoolSuccessorStageSelectedPoolEnough
          m w z q ⟨stage, by omega⟩ hstage
            (routedDepthOutputPathLast m w stage path)
            (nestedTensorHistoryAt
              (decodedRetryPoolSuccessorStageOutcome
                m w z q ⟨stage, by omega⟩ hstage)
              (logicalOutputCount m w) stage outcome.2
              ((decodedRetryPoolNestedPathEquiv m w stage).symm
                (routedDepthOutputPathInit m w stage path)))) :=
  rfl
end QEC.Distillation.HH18Parameterized
