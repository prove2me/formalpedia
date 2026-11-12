-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolShortageMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:30:12.963443+00:00
-- url     : https://prove2.me/submissions/85007002-dcb2-4823-b749-15d5d1eb0973

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
    0 ≤ decodedRetryPoolShortageMass h hdegree attempts required rho := by
  unfold decodedRetryPoolShortageMass
  exact Finset.sum_nonneg fun history _ =>
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight_nonneg
      ⟨history, PUnit.unit⟩ rho
end QEC.Distillation.HH18Parameterized
