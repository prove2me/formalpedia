-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:06:40.683538+00:00
-- url     : https://prove2.me/submissions/24de2cf1-422f-4c6d-8581-5780ff22feb1

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_bornWeight_eq_tensorPower
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerEnoughMass_add_tensorPowerShortageMass


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
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    decodedRetryPoolEnoughMass h hdegree attempts required rho +
        decodedRetryPoolShortageMass h hdegree attempts required rho = 1 := by
  unfold decodedRetryPoolEnoughMass decodedRetryPoolShortageMass
  simp_rw [decodedRetryPoolInstrument_bornWeight_eq_tensorPower]
  exact tensorPowerEnoughMass_add_tensorPowerShortageMass
    (decodedInstrument h hdegree) decodedRetryPoolAccepts attempts required rho
    (decodedInstrument_complete h hdegree)
end QEC.Distillation.HH18Parameterized
