-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.deriv_deriv_nonpos_of_isLocalMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:40:12.907193+00:00
-- url     : https://prove2.me/submissions/d2f72978-2864-41a7-9ff7-8c348ca07eba

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
theorem _root_.solution {g : ℝ → ℝ} (hmax : IsLocalMax g 0)
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ g t) : deriv (deriv g) 0 ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hd2 : DifferentiableAt ℝ (deriv g) 0 := by
    by_contra hnd
    rw [deriv_zero_of_not_differentiableAt hnd] at hpos
    exact lt_irrefl _ hpos
  have h0 : deriv g 0 = 0 := hmax.deriv_eq_zero
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd2.hasDerivAt
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < slope (deriv g) 0 t := hslope.eventually (lt_mem_nhds hpos)
  rw [eventually_nhdsWithin_iff] at hev
  have hmax' : ∀ᶠ y in 𝓝 (0:ℝ), g y ≤ g 0 := hmax
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((hev.and hd).and hmax')
  have ht : 0 < ε / 2 := half_pos hε
  have hdist : ∀ y ∈ Set.Icc (0:ℝ) (ε / 2), dist y 0 < ε := by
    intro y hy
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1]
    linarith [hy.2]
  have hcont : ContinuousOn g (Set.Icc 0 (ε / 2)) := fun y hy =>
    ((hball (hdist y hy)).1.2).continuousAt.continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ g (Set.Ioo 0 (ε / 2)) := fun y hy =>
    ((hball (hdist y (Set.Ioo_subset_Icc_self hy))).1.2).differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope g ht hcont hdiffOn
  have hcpos : 0 < deriv g c := by
    have h := (hball (hdist c (Set.Ioo_subset_Icc_self hc))).1.1
      (Set.mem_compl_singleton_iff.mpr hc.1.ne')
    simp only [slope_def_field, h0, sub_zero] at h
    exact (div_pos_iff_of_pos_right hc.1).mp h
  rw [hcd, sub_zero] at hcpos
  have hgt := (div_pos_iff_of_pos_right ht).mp hcpos
  have hle := (hball (hdist (ε / 2) ⟨ht.le, le_rfl⟩)).2
  linarith
end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
