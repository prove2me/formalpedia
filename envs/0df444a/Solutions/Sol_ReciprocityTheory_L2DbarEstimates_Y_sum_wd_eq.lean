-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.sum_wd_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:42:20.220809+00:00
-- url     : https://prove2.me/submissions/5e7683f6-8a20-4bba-978e-528a25378fa3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_clm_smul_decomp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_vec_expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
private theorem clm_apply_eq_sum_re_im_basis {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) :
    D ζ = ∑ k, ((ζ k).re * D (bas n k) + (ζ k).im * D (I • bas n k)) := by
  conv_lhs => rw [vec_expand ζ]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => clm_smul_decomp D (ζ k) (bas n k)
end
end ReciprocityTheory.L2DbarEstimates.Y
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} (g : V n → ℂ) (y : V n) (ζ : V n) :
    ∑ k, wd n k g y * ζ k = dv (fderiv ℝ g y) ζ := by
  unfold dv
  rw [clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) ζ, clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) (I • ζ), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [wd, PiLp.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
  apply Complex.ext <;> simp <;> ring
end ReciprocityTheory.L2DbarEstimates.Y
