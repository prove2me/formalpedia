-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_bornWeight_tensorPowerProductInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:07:04.582959+00:00
-- url     : https://prove2.me/submissions/63adc6ef-c139-4a2f-a27e-0282a96178ea

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_bornWeight_eq_tensorPower
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_tensorPower


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
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome attempts) :
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight
        ⟨history, PUnit.unit⟩
          (tensorPowerProductInput (prepareMeasuredResources m w inputs) rhoUnit attempts) =
      tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w inputs) attempts history := by
  rw [decodedRetryPoolInstrument_bornWeight_eq_tensorPower]
  exact bornWeight_tensorPower (decodedInstrument h hdegree)
    (prepareMeasuredResources m w inputs) rhoUnit attempts history
end QEC.Distillation.HH18Parameterized
