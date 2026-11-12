-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingMassAux_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:07:00.18755+00:00
-- url     : https://prove2.me/submissions/e83beb09-07f4-4339-89f6-0c93ba411d7f

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


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
attribute [local instance] QEC.Distillation.HH18Parameterized.instPhysicalSuccessMassRecurrenceClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instPhysicalSuccessMassRecurrenceClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    0 <= decodedRetryPoolProtocolSuccessfulRoutingMassAux
      h hdegree z q hz stage hstage rho := by
  unfold decodedRetryPoolProtocolSuccessfulRoutingMassAux
  exact Finset.sum_nonneg fun outcome _ =>
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz stage hstage).bornWeight_nonneg outcome rho
end QEC.Distillation.HH18Parameterized
