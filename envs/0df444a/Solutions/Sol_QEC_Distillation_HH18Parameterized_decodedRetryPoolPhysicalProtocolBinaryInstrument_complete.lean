-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolBinaryInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:06:05.248413+00:00
-- url     : https://prove2.me/submissions/d798ed3b-e694-4b1b-af39-f42e58a10cee

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolInstrument_complete


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
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) :
    (decodedRetryPoolPhysicalProtocolBinaryInstrument
      h hdegree z q hz).kraus.Complete :=
  binaryCoarsen_complete
    (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
    (decodedRetryPoolPhysicalProtocolInstrument_complete h hdegree z q hz)
end QEC.Distillation.HH18Parameterized
