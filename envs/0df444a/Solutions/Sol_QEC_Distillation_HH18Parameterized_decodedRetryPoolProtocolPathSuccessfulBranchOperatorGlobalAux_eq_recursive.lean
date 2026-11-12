-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_recursive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:23:28.017868+00:00
-- url     : https://prove2.me/submissions/a21eb5e6-a7a1-4b17-af6c-30cf07ea8fe4

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_succ
section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
private theorem decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_zero
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (path : routedDepthOutputSlots m w 0)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz 0 hz path rho =
      decodedRetryPoolProtocolRootSuccessfulBranchOperator
        h hdegree z q hz rho := by
  rfl
end HH18Parameterized
end Distillation
end QEC
end
end

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
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
          h hdegree z q hz stage hstage path rho =
        decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
          h hdegree z q hz rho stage hstage path := by
  intro stage
  induction stage with
  | zero =>
      intro hzero path
      rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_zero]
      rfl
  | succ stage ih =>
      intro hstage path
      rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_succ
        h hdegree z q hz ⟨stage, by omega⟩ hstage path rho]
      rw [ih (by omega) (routedDepthOutputPathInit m w stage path)]
      rfl
end QEC.Distillation.HH18Parameterized
