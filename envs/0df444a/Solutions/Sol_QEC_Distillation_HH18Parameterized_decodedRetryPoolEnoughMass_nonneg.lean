-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolEnoughMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:03:21.597659+00:00
-- url     : https://prove2.me/submissions/b4277a8d-e1ee-411c-ba36-dc2e74a95b9c

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


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
    0 ≤ decodedRetryPoolEnoughMass h hdegree attempts required rho := by
  unfold decodedRetryPoolEnoughMass
  exact Finset.sum_nonneg fun history _ =>
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight_nonneg
      ⟨history, PUnit.unit⟩ rho
end QEC.Distillation.HH18Parameterized
