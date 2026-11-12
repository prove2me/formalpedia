-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthTypedSuccessfulOutputCost_le_six_fifths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:20:11.575382+00:00
-- url     : https://prove2.me/submissions/a22b782b-2ea2-4d33-bfad-abae56b7bfe7

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_five_sixths_le
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthTypedSuccessfulOutputCost_eq

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
    (depth : Nat) :
    routedDepthTypedSuccessfulOutputCost h hdegree epsilon hsmall depth ≤
      (6 / 5 : ℝ) * ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth := by
  rw [routedDepthTypedSuccessfulOutputCost_eq]
  have hratioNonneg :
      0 ≤ ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  have hyield : (5 / 6 : ℝ) ≤
      (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) :=
    routedDepthPooledYield_five_sixths_le h hdegree epsilon hsmall depth
  calc
    ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth /
        (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) ≤
        ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth / ((5 : ℝ) / 6) :=
      div_le_div_of_nonneg_left hratioNonneg (by norm_num) hyield
    _ = (6 / 5 : ℝ) * ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth := by
      ring
end QEC.Distillation.HH18Parameterized
