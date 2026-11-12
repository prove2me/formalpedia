-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.acceptedResidualError_le_cubic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:01:43.280242+00:00
-- url     : https://prove2.me/submissions/6f85c3d6-1d19-423b-b261-5b6367ff7c10

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_pos
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawAcceptedResidualErrorMass_nonneg
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawAcceptedResidualErrorMass_le_card_cube
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_half_power_le

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualError epsilon ≤ residualCubicCoefficient * epsilon.1 ^ 3 := by
  unfold acceptedResidualError residualCubicCoefficient
  have hsuccess : 0 < rawSuccessMass epsilon := rawSuccessMass_pos epsilon
  have hmass : 0 ≤ rawAcceptedResidualErrorMass epsilon :=
    rawAcceptedResidualErrorMass_nonneg epsilon
  have hcube : 0 ≤ (Fintype.card PhysicalErrorWord : ℝ) * epsilon.1 ^ 3 := by
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg epsilon.property.1 _)
  calc
    rawAcceptedResidualErrorMass epsilon / rawSuccessMass epsilon ≤
        ((Fintype.card PhysicalErrorWord : ℝ) * epsilon.1 ^ 3) /
          rawSuccessMass epsilon := by
      exact div_le_div_of_nonneg_right
        (rawAcceptedResidualErrorMass_le_card_cube epsilon) hsuccess.le
    _ ≤ ((Fintype.card PhysicalErrorWord : ℝ) * epsilon.1 ^ 3) /
          ((1 / 2 : ℝ) ^ resourceCount) := by
      exact div_le_div_of_nonneg_left hcube
        (by positivity) (rawSuccessMass_half_power_le epsilon)
    _ = residualCubicCoefficient * epsilon.1 ^ 3 := by
      unfold residualCubicCoefficient
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
end QEC.Distillation.HH18Protocol
