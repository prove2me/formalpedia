-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolEnoughMass_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:11:44.653212+00:00
-- url     : https://prove2.me/submissions/bfebc5ef-7ffd-4ec3-a1cd-bfcd2502b8ba

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolShortageMass_nonneg
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass

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
    decodedRetryPoolEnoughMass h hdegree attempts required rho ≤ 1 := by
  have hpartition := decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass
    h hdegree attempts required rho
  have hshortage := decodedRetryPoolShortageMass_nonneg
    h hdegree attempts required rho
  linarith
end QEC.Distillation.HH18Parameterized
