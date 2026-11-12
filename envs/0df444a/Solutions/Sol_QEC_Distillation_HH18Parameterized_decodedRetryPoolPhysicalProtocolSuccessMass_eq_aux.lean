-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_eq_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:15:52.36832+00:00
-- url     : https://prove2.me/submissions/90f3e1a4-6e3f-4c18-8d5a-dca5ca8149d0

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolSuccessMass_eq_sum


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
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz rho =
      decodedRetryPoolProtocolSuccessfulRoutingMassAux
        h hdegree z q hz (z - 1) (by omega) rho := by
  rw [decodedRetryPoolPhysicalProtocolSuccessMass_eq_sum]
  rfl
end QEC.Distillation.HH18Parameterized
