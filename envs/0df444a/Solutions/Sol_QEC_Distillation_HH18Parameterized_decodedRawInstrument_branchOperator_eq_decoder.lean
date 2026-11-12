-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRawInstrument_branchOperator_eq_decoder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:16:17.894648+00:00
-- url     : https://prove2.me/submissions/42875bc9-57b1-497f-bec5-42b92b4a18b9

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_branchOperator_punit
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_inducedMap_apply


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (A : Operator (PhysicalRegister m w)) :
    (decodedRawInstrument h hdegree).branchOperator
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ A =
      decoderChannel h
        ((resourcePostselectionInstrument h hdegree).branchOperator
          ⟨PUnit.unit, outcome⟩ A) := by
  change
    ((resourcePostselectionInstrument h hdegree).bindDependent
      (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))).branchOperator
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ A = _
  rw [bindDependent_branchOperator_punit]
  exact QuantumChannel.toFiniteInstrument_inducedMap_apply (decoderChannel h) _
end QEC.Distillation.HH18Parameterized
