-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.acceptedResidualError_le_residualCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:15:22.346184+00:00
-- url     : https://prove2.me/submissions/904a5c5b-7694-4a98-9a25-aae1ef589723

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_half_power_le
import Theorems.Thm_QEC_Distillation_HH18Parameterized_rawAcceptedResidualErrorMass_nonneg
import Theorems.Thm_QEC_Distillation_HH18Parameterized_rawAcceptedResidualErrorMass_le_card_distance_pow
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualError h hdegree epsilon ≤
      residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by
  unfold acceptedResidualError residualCoefficient
  rw [endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon]
  have hsuccess : 0 < acceptedBernoulliMass w r m epsilon :=
    acceptedBernoulliMass_pos h epsilon
  have hmass : 0 ≤ rawAcceptedResidualErrorMass w r m epsilon :=
    rawAcceptedResidualErrorMass_nonneg w r m epsilon
  have hbound : 0 ≤ (Fintype.card (PhysicalErrorWord m w) : ℝ) *
      epsilon.1 ^ codeDistance r w := by
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg epsilon.property.1 _)
  calc
    rawAcceptedResidualErrorMass w r m epsilon / acceptedBernoulliMass w r m epsilon ≤
        ((Fintype.card (PhysicalErrorWord m w) : ℝ) * epsilon.1 ^ codeDistance r w) /
          acceptedBernoulliMass w r m epsilon := by
      exact div_le_div_of_nonneg_right
        (rawAcceptedResidualErrorMass_le_card_distance_pow h epsilon) hsuccess.le
    _ ≤ ((Fintype.card (PhysicalErrorWord m w) : ℝ) * epsilon.1 ^ codeDistance r w) /
          ((1 / 2 : ℝ) ^ physicalInputCount m w) := by
      exact div_le_div_of_nonneg_left hbound (by positivity)
        (acceptedBernoulliMass_half_power_le h epsilon)
    _ = residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by
      unfold residualCoefficient
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
end QEC.Distillation.HH18Parameterized
