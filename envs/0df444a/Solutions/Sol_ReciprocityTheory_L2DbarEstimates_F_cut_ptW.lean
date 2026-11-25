-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_ptW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:58.99556+00:00
-- url     : https://prove2.me/submissions/cf2cbbf7-236a-43ee-ad71-3bfc70837202

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_sq_sub_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
private lemma norm_ofReal_sq_le_one_of_abs_le_one (c : ℝ) (hc : |c| ≤ 1) : ‖(c : ℂ)‖ ^ 2 ≤ 1 := by
  have h1 : ‖(c : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hc
  nlinarith [norm_nonneg (c : ℂ)]
end
end ReciprocityTheory.L2DbarEstimates.F
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (c : ℝ) (hc : |c| ≤ 1) (wx S : ℂ) (fx2 D ph ψ : ℝ) (hS : ‖S‖ ^ 2 ≤ D * fx2)
    (hD : D ≤ Real.exp ψ) (hf2 : 0 ≤ fx2) :
    ‖(c : ℂ) * wx - (Real.exp (-ψ) : ℂ) * S‖ ^ 2 * Real.exp (-(ph - 2 * ψ)) ≤
      2 * (‖wx‖ ^ 2 * Real.exp (-(ph - 2 * ψ))) + 2 * (fx2 * Real.exp (-(ph - ψ))) := by
  have h1 := cut_sq_sub_le ((c : ℂ) * wx) ((Real.exp (-ψ) : ℂ) * S)
  have hc2 := norm_ofReal_sq_le_one_of_abs_le_one c hc
  have h2 : ‖(c : ℂ) * wx‖ ^ 2 ≤ ‖wx‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    nlinarith [mul_nonneg (sub_nonneg.2 hc2) (sq_nonneg ‖wx‖)]
  have h3 : ‖(Real.exp (-ψ) : ℂ) * S‖ ^ 2 = Real.exp (-ψ) ^ 2 * ‖S‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hP : 0 < Real.exp (-(ph - 2 * ψ)) := Real.exp_pos _
  have hPQ : Real.exp (-(ph - 2 * ψ)) = Real.exp (-(ph - ψ)) * Real.exp ψ := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hAB : Real.exp (-ψ) * Real.exp ψ = 1 := by
    rw [← Real.exp_add]
    simp
  have hS' : Real.exp (-ψ) ^ 2 * ‖S‖ ^ 2 ≤ Real.exp (-ψ) ^ 2 * (D * fx2) :=
    mul_le_mul_of_nonneg_left hS (sq_nonneg _)
  have hD' : Real.exp (-ψ) ^ 2 * (D * fx2) ≤ Real.exp (-ψ) ^ 2 * (Real.exp ψ * fx2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD hf2) (sq_nonneg _)
  calc ‖(c : ℂ) * wx - (Real.exp (-ψ) : ℂ) * S‖ ^ 2 * Real.exp (-(ph - 2 * ψ))
      ≤ (2 * ‖wx‖ ^ 2 + 2 * (Real.exp (-ψ) ^ 2 * (Real.exp ψ * fx2))) * Real.exp (-(ph - 2 * ψ)) := by
        apply mul_le_mul_of_nonneg_right _ hP.le
        linarith
    _ = 2 * (‖wx‖ ^ 2 * Real.exp (-(ph - 2 * ψ))) + 2 * (fx2 * Real.exp (-(ph - ψ))) := by
        rw [hPQ]
        linear_combination (2 * fx2 * Real.exp (-(ph - ψ)) * (Real.exp (-ψ) * Real.exp ψ + 1)) * hAB
end ReciprocityTheory.L2DbarEstimates.F
