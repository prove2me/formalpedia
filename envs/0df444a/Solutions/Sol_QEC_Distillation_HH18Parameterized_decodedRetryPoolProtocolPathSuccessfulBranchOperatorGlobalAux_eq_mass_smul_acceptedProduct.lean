-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_mass_smul_acceptedProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:58:37.378451+00:00
-- url     : https://prove2.me/submissions/02c27f45-a423-4536-97f6-a86d688ccdc7

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_recursive
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_eq_mass_smul_acceptedProduct


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
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
          h hdegree z q hz stage hstage path
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit) =
        (decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage hstage path : Complex) •
          (decodedRetryPoolAcceptedProductDensity h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage path)
            rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q
              ⟨stage, hstage⟩)).toOperator := by
  intro stage hstage path
  rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_recursive]
  exact
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_eq_mass_smul_acceptedProduct
      h hdegree epsilon hsmall z q hz rhoUnit stage hstage path
end QEC.Distillation.HH18Parameterized
