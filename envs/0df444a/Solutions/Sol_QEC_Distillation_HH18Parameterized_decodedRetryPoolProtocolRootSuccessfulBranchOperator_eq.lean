-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolRootSuccessfulBranchOperator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:17:31.042576+00:00
-- url     : https://prove2.me/submissions/8f0671db-d621-4606-ba35-14db77ca8a6d

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPool_enoughBranch_sum_eq_enoughMass_smul_acceptedProduct


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
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolProtocolRootSuccessfulBranchOperator h hdegree z q hz
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit) =
      (decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)).toOperator := by
  exact
    (decodedRetryPool_enoughBranch_sum_eq_enoughMass_smul_acceptedProduct
      h hdegree epsilon rhoUnit
      (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩))
end QEC.Distillation.HH18Parameterized
