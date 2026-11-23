-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_clm_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:55.044026+00:00
-- url     : https://prove2.me/submissions/79fadb8e-9473-44d4-821d-a4df24d1d26f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open Filter Topology Set ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (n : ℕ) (D : V n →L[ℝ] ℂ) (u : V n) :
    D u = ∑ a, ((D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2 * u a +
      (D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2 * (starRingEnd ℂ) (u a)) := by
  have hu : u = ∑ a, ((u a).re • bas n a + (u a).im • (Complex.I • bas n a)) := by
    ext b
    simp [bas, EuclideanSpace.single_apply, Finset.sum_add_distrib, Complex.real_smul,
      Pi.single_apply, mul_ite, mul_one, mul_zero]
  conv_lhs => rw [hu]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have h1 : u a = ((u a).re : ℂ) + ((u a).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : (starRingEnd ℂ) (u a) = ((u a).re : ℂ) - ((u a).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2) * h1 +
    (-(D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2) * h2 +
    (((u a).im : ℂ) * D (Complex.I • bas n a)) * Complex.I_mul_I
end ReciprocityTheory.L2DbarEstimates.Y
