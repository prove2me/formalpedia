-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_observe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:41:07.178741+00:00
-- url     : https://prove2.me/submissions/42469ec4-75a8-4846-ba03-01540160d169

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_observe


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
    (firstIndex : tensorPowerHistory (decodedRawIndex h hdegree) attempts)
    (secondIndex : Fin ((tensorPowerHistoryConditionedChannel
      decodedRetryPoolAccepts attempts
      (((decodedInstrument h hdegree).tensorPower attempts).observe firstIndex)
      required (LogicalSite m w)
      (decodedRetryPoolShortageState m w required)).chosenKrausCount)) :
    (decodedRetryPoolInstrument h hdegree attempts required).observe
      ⟨firstIndex, secondIndex⟩ =
        ⟨((decodedInstrument h hdegree).tensorPower attempts).observe firstIndex,
          PUnit.unit⟩ := by
  exact tensorPowerHistoryConditionedInstrument_observe
    (decodedInstrument h hdegree) decodedRetryPoolAccepts attempts required
    (decodedRetryPoolShortageState m w required) firstIndex secondIndex
end QEC.Distillation.HH18Parameterized
