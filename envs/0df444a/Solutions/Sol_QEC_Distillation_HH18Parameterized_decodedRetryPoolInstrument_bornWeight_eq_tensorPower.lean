-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_bornWeight_eq_tensorPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:02:32.388111+00:00
-- url     : https://prove2.me/submissions/01741189-e5db-4294-9a63-fbb439a28a6e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_bornWeight_eq_tensorPower_bornWeight


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (history : tensorPowerHistory DistillationOutcome attempts)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight
        ⟨history, PUnit.unit⟩ rho =
      ((decodedInstrument h hdegree).tensorPower attempts).bornWeight history rho := by
  exact tensorPowerHistoryConditionedInstrument_bornWeight_eq_tensorPower_bornWeight
    (decodedInstrument h hdegree) decodedRetryPoolAccepts attempts required
    (decodedRetryPoolShortageState m w required) history rho
end QEC.Distillation.HH18Parameterized
