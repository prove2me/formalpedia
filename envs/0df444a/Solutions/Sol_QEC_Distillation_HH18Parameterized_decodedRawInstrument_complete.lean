-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRawInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:56:58.91112+00:00
-- url     : https://prove2.me/submissions/704d8102-7c0f-4e08-9d87-ce585ba6a8e7

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Theorems.Thm_QEC_Distillation_HH18Parameterized_resourcePostselectionInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedInstrumentClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (decodedRawInstrument h hdegree).kraus.Complete := by
  exact FiniteInstrument.bindDependent_complete
    (resourcePostselectionInstrument h hdegree)
    (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))
    (resourcePostselectionInstrument_complete h hdegree)
    (fun _ => QuantumChannel.toFiniteInstrument_complete (decoderChannel h))
end QEC.Distillation.HH18Parameterized
