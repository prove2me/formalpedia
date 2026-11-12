-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolStageTransitionInstrument_sum_bornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:49:59.29623+00:00
-- url     : https://prove2.me/submissions/7568b207-c0d7-4088-9b36-c9bebe2bedfc

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolStageTransitionInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one


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
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q stage))) :
    ∑ outcome,
        (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).bornWeight
          outcome rho = 1 :=
  (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).sum_bornWeight_eq_one
    (decodedRetryPoolStageTransitionInstrument_complete h hdegree z q stage hstage) rho
end QEC.Distillation.HH18Parameterized
