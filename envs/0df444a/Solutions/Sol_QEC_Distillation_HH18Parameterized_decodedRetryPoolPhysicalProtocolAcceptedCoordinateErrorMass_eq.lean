-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:19:39.655712+00:00
-- url     : https://prove2.me/submissions/cf8e43cd-aff7-4bb3-8977-90535f368635

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
import Definitions.Def_QEC_Semantics_Instruments_Branches_FilteredBranchMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryCoarsen_branchOperator_accepted
import Theorems.Thm_QEC_Semantics_FiniteInstrument_filteredBranchOperatorSum_eq_sum_filter


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
        h hdegree z q hz rho coordinate =
      Complex.re (LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator .negative
          ((decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
            m w z q hz coordinate)
            (filteredBranchOperatorSum
              (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
              (fun outcome =>
                decodedRetryPoolPhysicalProtocolSuccessfulRouting
                  m w z q hz outcome = true)
              rho.toOperator)))) := by
  unfold decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
    decodedRetryPoolPhysicalProtocolBinaryInstrument
  rw [binaryCoarsen_branchOperator_accepted]
  rw [filteredBranchOperatorSum_eq_sum_filter]
end QEC.Distillation.HH18Parameterized
