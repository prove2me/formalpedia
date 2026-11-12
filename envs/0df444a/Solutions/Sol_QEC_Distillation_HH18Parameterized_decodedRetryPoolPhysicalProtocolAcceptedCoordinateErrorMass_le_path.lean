-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:24:44.457205+00:00
-- url     : https://prove2.me/submissions/6b222ea4-c35e-4347-9dfd-1bd8836fd93e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
import Definitions.Def_QEC_Semantics_Instruments_Branches_FilteredBranchMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_eq
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolSuccessfulRoutingAux_implies_path
import Theorems.Thm_QEC_Semantics_FiniteInstrument_filteredBranchMeasuredTrace_mono

section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
private theorem decodedRetryPoolPhysicalProtocolPathFilteredCoordinate_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    (decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
      m w z q hz coordinate)
        (filteredBranchOperatorSum
          (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
          (fun outcome =>
            decodedRetryPoolProtocolPathSuccessfulRoutingAux
              m w z q (z - 1) (by omega) coordinate.1 outcome = true)
          rho.toOperator) =
      (decodedRetryPoolAcceptedProductCoordinateChannel m w
        (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz))
        coordinate.2.1 coordinate.2.2)
        (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
          h hdegree z q hz (z - 1) (by omega) coordinate.1 rho) := by
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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
        h hdegree z q hz rho coordinate <=
      Complex.re (LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator .negative
          ((decodedRetryPoolAcceptedProductCoordinateChannel m w
            (decodedRetryPoolBackwardSchedule m w z q
              (decodedRetryPoolProtocolTerminalStage z hz))
            coordinate.2.1 coordinate.2.2)
            (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
              h hdegree z q hz (z - 1) (by omega) coordinate.1 rho)))) := by
  rw [decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_eq]
  rw [← decodedRetryPoolPhysicalProtocolPathFilteredCoordinate_eq
    h hdegree z q hz rho coordinate]
  apply filteredBranchMeasuredTrace_mono
  intro outcome hglobal
  exact decodedRetryPoolProtocolSuccessfulRoutingAux_implies_path
    m w z q (z - 1) (by omega) outcome hglobal coordinate.1
end QEC.Distillation.HH18Parameterized
