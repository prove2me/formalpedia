-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedInstrument_bornWeight_eq_resourcePostselection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:57:54.249918+00:00
-- url     : https://prove2.me/submissions/8a96e189-bc2e-451a-b642-b611d307fdfe

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_bornWeight_eq_decodedRawInstrument
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_bornWeight_punit
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
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    (decodedInstrument h hdegree).bornWeight outcome rho =
      (resourcePostselectionInstrument h hdegree).bornWeight
        ⟨PUnit.unit, outcome⟩ rho := by
  rw [decodedInstrument_bornWeight_eq_decodedRawInstrument]
  change ((resourcePostselectionInstrument h hdegree).bindDependent
      (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))).bornWeight
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ rho = _
  exact FiniteInstrument.bindDependent_bornWeight_punit
    (resourcePostselectionInstrument h hdegree)
    (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))
    (fun _ => QuantumChannel.toFiniteInstrument_complete (decoderChannel h))
    ⟨PUnit.unit, outcome⟩ rho
end QEC.Distillation.HH18Parameterized
