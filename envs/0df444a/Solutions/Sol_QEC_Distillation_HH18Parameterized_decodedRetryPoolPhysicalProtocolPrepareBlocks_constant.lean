-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolPrepareBlocks_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:18:54.561197+00:00
-- url     : https://prove2.me/submissions/57c97cdc-ef2d-4772-95f3-1b83e2b6e4f1

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
    {m w attempts : Nat}
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (rho : DensityOperator (PhysicalRegister m w)) :
    decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit attempts
        (fun _ : Fin attempts => rho) =
      tensorPowerProductInput rho rhoUnit attempts := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      change DensityOperator.tensorDensity rho
          (decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit attempts
            (fun _ : Fin attempts => rho)) =
        DensityOperator.tensorDensity rho
          (tensorPowerProductInput rho rhoUnit attempts)
      rw [ih]
end QEC.Distillation.HH18Parameterized
