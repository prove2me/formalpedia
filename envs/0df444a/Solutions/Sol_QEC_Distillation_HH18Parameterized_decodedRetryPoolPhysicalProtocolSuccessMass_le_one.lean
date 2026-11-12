-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:06:56.751472+00:00
-- url     : https://prove2.me/submissions/5fc91771-70f4-46c4-b4df-836e7a292cd7

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
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz rho <= 1 :=
  binaryCoarsen_accepted_le_one
    (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
    (decodedRetryPoolPhysicalProtocolInstrument_complete h hdegree z q hz) rho
end QEC.Distillation.HH18Parameterized
