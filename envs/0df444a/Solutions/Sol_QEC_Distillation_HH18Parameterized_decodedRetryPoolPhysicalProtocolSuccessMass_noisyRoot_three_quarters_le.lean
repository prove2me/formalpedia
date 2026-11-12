-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_three_quarters_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:38:26.243196+00:00
-- url     : https://prove2.me/submissions/341a9b6f-0496-49ab-ba38-ddf70ad8dbba

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageFailurePathBound
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessLowerBound
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_lower_bound
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolStageAggregateShortageBudget_sum_le_one_quarter


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
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (3 / 4 : Real) ≤
      decodedRetryPoolPhysicalProtocolSuccessMass
        h hdegree z q hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) := by
  have hsmall :=
    decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
      epsilon hpool
  have hlower := decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_lower_bound
    h hdegree epsilon hsmall z q hz rhoUnit
  have hbudget := decodedRetryPoolStageAggregateShortageBudget_sum_le_one_quarter
    h epsilon hpool z
  linarith
end QEC.Distillation.HH18Parameterized
