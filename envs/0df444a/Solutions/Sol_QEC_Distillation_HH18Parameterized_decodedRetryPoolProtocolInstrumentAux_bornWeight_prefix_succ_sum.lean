-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_bornWeight_prefix_succ_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:12:10.940123+00:00
-- url     : https://prove2.me/submissions/e28488ba-a0f1-439f-976d-209029456dce

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
import Definitions.Def_QEC_Semantics_Instruments_Sequential_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_BornMass
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolNestedSuccessorStageInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_bornWeight_fst_sum


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
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q stage (by omega)) :
    (∑ nextOutcome : nestedTensorHistory
        (decodedRetryPoolSuccessorStageOutcome
          m w z q ⟨stage, by omega⟩ hstage)
        (logicalOutputCount m w) stage,
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz (stage + 1) hstage).bornWeight
          ⟨outcome, nextOutcome⟩ rho) =
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz stage (by omega)).bornWeight outcome rho := by
  change
    (∑ nextOutcome,
      ((decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage (by omega)).bind
        (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage)).bornWeight
            ⟨outcome, nextOutcome⟩ rho) = _
  exact bind_bornWeight_fst_sum
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz stage (by omega))
    (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
      h hdegree z q stage hstage)
    (fun _ => decodedRetryPoolNestedSuccessorStageInstrument_complete
      h hdegree z q ⟨stage, by omega⟩ hstage)
    outcome rho
end QEC.Distillation.HH18Parameterized
