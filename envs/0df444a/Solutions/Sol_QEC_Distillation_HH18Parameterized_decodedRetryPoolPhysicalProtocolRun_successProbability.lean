-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_successProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:27:54.950285+00:00
-- url     : https://prove2.me/submissions/f4b7a739-79e5-47c4-b2de-553a69b585ff

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessLowerBound
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolPrepareResources_noisyResources

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalProtocolRun
        h hdegree epsilon z q hz rhoUnit).successProbability =
      decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz
        (decodedRetryPoolPhysicalProtocolNoisyRootInput m w z q hz epsilon
          rhoUnit) := by
  change decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz
      (decodedRetryPoolPhysicalProtocolPrepareResources m w
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) rhoUnit
        (decodedRetryPoolPhysicalProtocolNoisyResources m w z q hz epsilon)) = _
  rw [decodedRetryPoolPhysicalProtocolPrepareResources_noisyResources]
end QEC.Distillation.HH18Parameterized
