-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedInstrument_observe
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T18:46:44.532203+00:00
-- url     : https://prove2.me/submissions/eee582d9-e4c9-40c8-8e14-f60756f183f5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
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

theorem solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (index : decodedRawIndex h hdegree) :
    (decodedInstrument h hdegree).observe index =
      (postselectionInstrument h).observe index.1.2 := rfl