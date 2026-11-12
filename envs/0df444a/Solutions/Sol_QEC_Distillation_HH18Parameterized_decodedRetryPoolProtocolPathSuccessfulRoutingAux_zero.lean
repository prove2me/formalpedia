-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:07:08.917132+00:00
-- url     : https://prove2.me/submissions/94863298-ecdb-476f-8c23-27d99079cd09

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent

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
    (m w z q : Nat) (hz : 0 < z)
    (path : routedDepthOutputSlots m w 0)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q 0 hz) :
    decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q 0 hz path outcome =
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩) outcome :=
  rfl
end QEC.Distillation.HH18Parameterized
