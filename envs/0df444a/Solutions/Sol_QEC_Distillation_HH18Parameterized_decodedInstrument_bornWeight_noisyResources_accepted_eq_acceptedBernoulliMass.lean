-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedInstrument_bornWeight_noisyResources_accepted_eq_acceptedBernoulliMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:13:58.114851+00:00
-- url     : https://prove2.me/submissions/e068ad2f-8082-45fe-a3ff-e4f4b1dee22c

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_bornWeight_prepareMeasuredResources
import Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_eq_acceptedBernoulliMass


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
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (decodedInstrument h hdegree).bornWeight .accepted
        (prepareMeasuredResources m w (noisyResources m w epsilon)) =
      acceptedBernoulliMass w r m epsilon := by
  rw [decodedInstrument_bornWeight_prepareMeasuredResources]
  exact endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon
end QEC.Distillation.HH18Parameterized
