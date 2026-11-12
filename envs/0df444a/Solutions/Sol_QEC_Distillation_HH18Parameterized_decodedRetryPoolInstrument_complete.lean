-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:06:13.950974+00:00
-- url     : https://prove2.me/submissions/bbccef52-6809-4abf-87a3-c985a80ae2de

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_complete


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
    (attempts required : Nat) :
    (decodedRetryPoolInstrument h hdegree attempts required).kraus.Complete :=
  tensorPowerHistoryConditionedInstrument_complete (decodedInstrument h hdegree)
    decodedRetryPoolAccepts attempts required
    (decodedRetryPoolShortageState m w required)
    (decodedInstrument_complete h hdegree)
end QEC.Distillation.HH18Parameterized
