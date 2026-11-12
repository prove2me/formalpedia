-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:06:56.20095+00:00
-- url     : https://prove2.me/submissions/990bd9bb-8248-4e97-aaae-d645d368d153

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryCoarsen_bornWeight_accepted


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
    decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz rho =
      ∑ outcome ∈ Finset.univ.filter
          (fun outcome =>
            decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz outcome),
        (decodedRetryPoolPhysicalProtocolInstrument
          h hdegree z q hz).bornWeight outcome rho := by
  exact binaryCoarsen_bornWeight_accepted
    (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz) rho
end QEC.Distillation.HH18Parameterized
