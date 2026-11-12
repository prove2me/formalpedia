-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicEnoughMass_noisyResources_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:35:00.385974+00:00
-- url     : https://prove2.me/submissions/b5fa2481-a542-47d3-bd85-d91a992e1431

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolDyadicShortageMass_le_noisyResources
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass


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
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolDyadicSlackClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (stage required : Nat) :
    1 - (decodedRetryPoolDyadicDenominator stage : ℝ) *
        physicalInputCount m w * epsilon.1 ≤
      decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolDyadicAttempts stage required) required
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          (decodedRetryPoolDyadicAttempts stage required)) := by
  have hshortage := decodedRetryPoolDyadicShortageMass_le_noisyResources
    h hdegree epsilon rhoUnit stage required
  have hpartition := decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass
    h hdegree (decodedRetryPoolDyadicAttempts stage required) required
    (tensorPowerProductInput
      (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
      (decodedRetryPoolDyadicAttempts stage required))
  linarith
end QEC.Distillation.HH18Parameterized
