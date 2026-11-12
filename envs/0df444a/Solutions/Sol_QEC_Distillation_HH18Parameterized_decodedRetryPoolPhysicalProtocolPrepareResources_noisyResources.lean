-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolPrepareResources_noisyResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:23:36.755198+00:00
-- url     : https://prove2.me/submissions/4f2069a4-4739-4f36-83a6-9c4eb4ed1c4f

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessLowerBound
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolPrepareBlocks_constant

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
    (m w z q : Nat) (hz : 0 < z)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalProtocolPrepareResources m w
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) rhoUnit
        (decodedRetryPoolPhysicalProtocolNoisyResources m w z q hz epsilon) =
      decodedRetryPoolPhysicalProtocolNoisyRootInput m w z q hz epsilon
        rhoUnit := by
  change decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit _
      (fun _ => prepareMeasuredResources m w (noisyResources m w epsilon)) = _
  exact decodedRetryPoolPhysicalProtocolPrepareBlocks_constant rhoUnit
    (prepareMeasuredResources m w (noisyResources m w epsilon))
end QEC.Distillation.HH18Parameterized
