-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.resourcePostselectionInstrument_bornWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:30:07.283833+00:00
-- url     : https://prove2.me/submissions/7b79c0b6-ec3d-49be-834d-71035d6b0a1d

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Theorems.Thm_QEC_Distillation_HH18Parameterized_resourcePostselectionInstrument_branchOperator

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
    (resourcePostselectionInstrument h hdegree).bornWeight
        ⟨PUnit.unit, outcome⟩ rho =
      postselectionWeight h outcome
        ((resourceConsumerChannel h hdegree).mapDensity rho) := by
  unfold postselectionWeight FiniteInstrument.bornWeight
  rw [resourcePostselectionInstrument_branchOperator h hdegree outcome rho.toOperator]
  rfl
end QEC.Distillation.HH18Parameterized
