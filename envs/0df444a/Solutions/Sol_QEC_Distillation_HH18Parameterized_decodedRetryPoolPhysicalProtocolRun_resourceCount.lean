-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_resourceCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:58:43.399202+00:00
-- url     : https://prove2.me/submissions/828a46a9-2433-45e1-91b8-be8925b12106

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessLowerBound
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run

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
      h hdegree epsilon z q hz rhoUnit).resourceCount =
      physicalInputCount m w *
        decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩ :=
  rfl
end QEC.Distillation.HH18Parameterized
