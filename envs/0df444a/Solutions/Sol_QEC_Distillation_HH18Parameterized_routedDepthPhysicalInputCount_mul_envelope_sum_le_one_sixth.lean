-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPhysicalInputCount_mul_envelope_sum_le_one_sixth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:01:31.79081+00:00
-- url     : https://prove2.me/submissions/b55f4c21-94c6-4a1c-8350-8b31f796c4ae

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Theorems.Thm_QEC_Distillation_HH18Parameterized_two_mul_routedDepthPhysicalInputCount_le_iterationScale
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_sum_le

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
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    (physicalInputCount m w : ℝ) *
      (∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1) ≤
        1 / 6 := by
  have hcountNonneg : 0 ≤ (physicalInputCount m w : ℝ) := Nat.cast_nonneg _
  have hcountScale := two_mul_routedDepthPhysicalInputCount_le_iterationScale w r m
  have hscaledProduct :
      (2 * (physicalInputCount m w : ℝ)) * epsilon.1 ≤
        routedDepthIterationScale w r m * epsilon.1 := by
    exact mul_le_mul_of_nonneg_right hcountScale epsilon.property.1
  change routedDepthIterationScale w r m * epsilon.1 ≤ 1 / 4 at hsmall
  have hcountEpsilon : (physicalInputCount m w : ℝ) * epsilon.1 ≤ 1 / 8 := by
    nlinarith [hscaledProduct, hsmall]
  calc
    (physicalInputCount m w : ℝ) *
        (∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1) ≤
        (physicalInputCount m w : ℝ) * ((4 / 3 : ℝ) * epsilon.1) :=
      mul_le_mul_of_nonneg_left
        (routedDepthErrorEnvelope_sum_le h epsilon hsmall depth) hcountNonneg
    _ = (4 / 3 : ℝ) * ((physicalInputCount m w : ℝ) * epsilon.1) := by ring
    _ ≤ (4 / 3 : ℝ) * (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hcountEpsilon (by norm_num)
    _ = 1 / 6 := by norm_num
end QEC.Distillation.HH18Parameterized
