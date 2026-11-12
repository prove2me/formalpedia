-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRootInputSlots_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:14:40.165116+00:00
-- url     : https://prove2.me/submissions/84eb2c6e-583c-4d73-bc65-4b931ab811d5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolBackwardRootRawCarrier_card


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
    (m w z q : Nat) (hz : 0 < z) :
    Fintype.card (decodedRetryPoolPhysicalProtocolRootInputSlots m w z q hz) =
      physicalInputCount m w *
        decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩ :=
  decodedRetryPoolBackwardRootRawCarrier_card m w z q hz
end QEC.Distillation.HH18Parameterized
