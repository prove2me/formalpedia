-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathRate_append_le_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:58:11.038663+00:00
-- url     : https://prove2.me/submissions/6f29db5c-d9ab-4feb-bcff-c5fb7fff6942

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_append_eq_rawError
section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
private theorem routedDepthSelectedRawError_le_rate_div_four_of_scaled
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (hscaled : routedDepthIterationScale w r m * rate.1 ≤ 1 / 4)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree rate port ≤ rate.1 / 4 := by
  have hdistance : 2 ≤ codeDistance r w := codeDistance_two_le h
  have hpred : 1 ≤ codeDistance r w - 1 := by
    omega
  have hraw := selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
    h hdegree rate port
  have hdomination := routedDepthRawErrorCoefficient_le_scale_pow_pred h
  have hrateNonneg : 0 ≤ rate.1 := rate.property.1
  have hscaleNonneg : 0 ≤ routedDepthIterationScale w r m :=
    (routedDepthIterationScale_pos w r m).le
  have hpower :
      (routedDepthIterationScale w r m * rate.1) ^ (codeDistance r w - 1) ≤
        1 / 4 := by
    calc
      (routedDepthIterationScale w r m * rate.1) ^ (codeDistance r w - 1) ≤
          (1 / 4 : ℝ) ^ (codeDistance r w - 1) :=
        pow_le_pow_left₀ (mul_nonneg hscaleNonneg hrateNonneg) hscaled _
      _ ≤ (1 / 4 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hpred
      _ = 1 / 4 := by norm_num
  have hfactor :
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          rate.1 ^ codeDistance r w =
        rate.1 * (routedDepthIterationScale w r m * rate.1) ^
          (codeDistance r w - 1) := by
    rw [mul_pow]
    have hsub : codeDistance r w - 1 + 1 = codeDistance r w :=
      Nat.sub_add_cancel (by omega)
    calc
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          rate.1 ^ codeDistance r w =
          routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            rate.1 ^ (codeDistance r w - 1 + 1) := by rw [hsub]
      _ = routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            (rate.1 ^ (codeDistance r w - 1) * rate.1) := by rw [pow_succ]
      _ = rate.1 * (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            rate.1 ^ (codeDistance r w - 1)) := by ring
  calc
    selectedLogicalPortRawError h hdegree rate port ≤
        routedDepthRawErrorCoefficient w r m * rate.1 ^ codeDistance r w :=
      hraw
    _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          rate.1 ^ codeDistance r w :=
      mul_le_mul_of_nonneg_right hdomination (pow_nonneg hrateNonneg _)
    _ = rate.1 * (routedDepthIterationScale w r m * rate.1) ^
          (codeDistance r w - 1) := hfactor
    _ ≤ rate.1 * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower hrateNonneg
    _ = rate.1 / 4 := by ring
end HH18Parameterized
end Distillation
end QEC
end
end

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
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port)).1 ≤
        (routedDepthPathRate h hdegree epsilon hsmall depth path).1 / 4 := by
  rw [routedDepthPathRate_append_eq_rawError]
  exact routedDepthSelectedRawError_le_rate_div_four_of_scaled h hdegree
    (routedDepthPathRate h hdegree epsilon hsmall depth path)
    (routedDepthPathRate_scaled_small h hdegree epsilon hsmall depth path) port
end QEC.Distillation.HH18Parameterized
