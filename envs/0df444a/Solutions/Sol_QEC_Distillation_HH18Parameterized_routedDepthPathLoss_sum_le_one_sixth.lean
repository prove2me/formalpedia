-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathLoss_sum_le_one_sixth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:07:04.750325+00:00
-- url     : https://prove2.me/submissions/304915a7-ef9e-45e6-8b4b-489666e2e1c3

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathStageRate_le_errorEnvelope
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPhysicalInputCount_mul_envelope_sum_le_one_sixth


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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    ∑ stage : Fin depth, (physicalInputCount m w : ℝ) *
      (routedDepthPathRate h hdegree epsilon hsmall stage.1
        (routedDepthPathStagePath m w depth path stage)).1 ≤ 1 / 6 := by
  rw [← Finset.mul_sum]
  calc
    (physicalInputCount m w : ℝ) *
        ∑ stage : Fin depth,
          (routedDepthPathRate h hdegree epsilon hsmall stage.1
            (routedDepthPathStagePath m w depth path stage)).1 ≤
        (physicalInputCount m w : ℝ) *
          ∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun stage _ =>
          routedDepthPathStageRate_le_errorEnvelope h hdegree epsilon hsmall depth path stage)
        (Nat.cast_nonneg _)
    _ ≤ 1 / 6 :=
      routedDepthPhysicalInputCount_mul_envelope_sum_le_one_sixth
        h epsilon hsmall depth
end QEC.Distillation.HH18Parameterized
