-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_scaled_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:45:17.323618+00:00
-- url     : https://prove2.me/submissions/0aa3fa4d-179f-499c-acf0-8ccf463d9ef2

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_closed_form

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
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    routedDepthIterationScale w r m *
      routedDepthErrorEnvelope w r m epsilon depth ≤ 1 / 4 := by
  rw [routedDepthErrorEnvelope_closed_form h epsilon]
  have hbase : 0 ≤ routedDepthIterationScale w r m * epsilon.1 :=
    mul_nonneg (routedDepthIterationScale_pos w r m).le epsilon.property.1
  have hdistance : 2 ≤ codeDistance r w := codeDistance_two_le h
  have hpower : 1 ≤ codeDistance r w ^ depth :=
    one_le_pow₀ (by omega)
  calc
    (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ depth) ≤
        (1 / 4 : ℝ) ^ (codeDistance r w ^ depth) :=
      pow_le_pow_left₀ hbase hsmall _
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hpower
    _ = 1 / 4 := by norm_num
end QEC.Distillation.HH18Parameterized
