-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.resourcePostselectionInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:29:33.968985+00:00
-- url     : https://prove2.me/submissions/8357d698-2464-4dbc-aaeb-3f280dd89e02

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionInstrument_complete
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
    (resourcePostselectionInstrument h hdegree).kraus.Complete := by
  exact FiniteInstrument.bindDependent_complete
    (QuantumChannel.toFiniteInstrument (resourceConsumerChannel h hdegree))
    (fun _ => postselectionInstrument h)
    (QuantumChannel.toFiniteInstrument_complete (resourceConsumerChannel h hdegree))
    (fun _ => postselectionInstrument_complete h)
end QEC.Distillation.HH18Parameterized
