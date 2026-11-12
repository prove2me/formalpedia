-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedInstrument_bornWeight_prepareMeasuredResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:03:32.592228+00:00
-- url     : https://prove2.me/submissions/44d2e80e-aa32-4e2f-8519-70d8cd43f9f4

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Theorems.Thm_QEC_Distillation_HH18Parameterized_resourcePostselectionInstrument_bornWeight
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_bornWeight_eq_resourcePostselection

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
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) :
    (decodedInstrument h hdegree).bornWeight outcome
        (prepareMeasuredResources m w inputs) =
      endpointWeight h hdegree inputs outcome := by
  rw [decodedInstrument_bornWeight_eq_resourcePostselection,
    resourcePostselectionInstrument_bornWeight]
  rfl
end QEC.Distillation.HH18Parameterized
