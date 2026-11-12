-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:58:25.723512+00:00
-- url     : https://prove2.me/submissions/d9db0db2-33dd-4230-b91f-4a0244b04dca

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z q stage : Nat) (hstage : stage + 1 < z)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q (stage + 1) hstage) :
    decodedRetryPoolProtocolSuccessfulRoutingAux
        m w z q (stage + 1) hstage outcome =
      (decodedRetryPoolProtocolSuccessfulRoutingAux
          m w z q stage (by omega) outcome.1 &&
        nestedTensorHistoryAll
          (decodedRetryPoolSuccessorStageRoutingGood
            m w z q ⟨stage, by omega⟩ hstage)
          (logicalOutputCount m w) stage outcome.2) :=
  rfl
end QEC.Distillation.HH18Parameterized
