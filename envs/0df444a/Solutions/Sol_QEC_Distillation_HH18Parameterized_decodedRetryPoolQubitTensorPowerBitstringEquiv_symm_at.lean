-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:24:17.56502+00:00
-- url     : https://prove2.me/submissions/b5a6104d-d84e-4cd8-a527-b52a851dc4a7

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (ι : Type) [Fintype ι] (bits : Bitstring ι)
    (coordinate : Fin (Fintype.card ι)) :
    tensorPowerHistoryAt (Fin 2) (Fintype.card ι)
        ((decodedRetryPoolQubitTensorPowerBitstringEquiv ι).symm bits) coordinate =
      bits ((Fintype.equivFin ι).symm coordinate) := by
  change tensorPowerHistoryAt (Fin 2) (Fintype.card ι)
      (tensorPowerHistoryOf (Fin 2) (Fintype.card ι)
        (fun trial => bits ((Fintype.equivFin ι).symm trial))) coordinate = _
  exact congrFun
    (tensorPowerHistoryAt_of (Fin 2) (Fintype.card ι)
      (fun trial => bits ((Fintype.equivFin ι).symm trial))) coordinate
end QEC.Distillation.HH18Parameterized
