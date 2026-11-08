-- Prove2me | solution 1 for ShippingContracts.expected_sales_gt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:48:54.938193+00:00
-- url     : https://prove2.me/submissions/eb281a92-11cd-4ac8-8cf9-2a907cb0775d

import Mathlib
import Definitions.Def_ShippingContracts_Model

open MeasureTheory ProbabilityTheory

namespace Aux_Ship_sales
open ShippingContracts MeasureTheory ProbabilityTheory Filter Topology Set

theorem F0 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ) : cdf μ 0 = 0 := by
  have hneg : μ (Iio 0) = 0 := by
    have := ae_iff.mp hD.nonneg
    have e : Iio (0 : ℝ) = {a | ¬ 0 ≤ a} := by ext a; simp
    rw [e]; exact this
  have hlt : ∀ t < 0, cdf μ t = 0 := by
    intro t ht
    rw [cdf_eq_real]
    have : μ (Iic t) = 0 := measure_mono_null (Iic_subset_Iio.mpr ht) hneg
    simp [measureReal_def, this]
  have h1 : Tendsto (cdf μ) (𝓝[<] (0 : ℝ)) (𝓝 (cdf μ 0)) :=
    (hD.continuous_cdf.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (cdf μ) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hlt t ht).symm
  exact tendsto_nhds_unique h1 h2

end Aux_Ship_sales

open ShippingContracts MeasureTheory ProbabilityTheory Filter Topology Set Aux_Ship_sales in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ)
    (x : ℝ) (hx : 0 < x) :
    ∫ d, min x d ∂μ = x - ∫ t in (0 : ℝ)..x, cdf μ t ∧
    x * (1 - cdf μ x) < ∫ d, min x d ∂μ := by
  have hint : Integrable (fun d => min x d) μ := by
    refine Integrable.mono' ((integrable_const |x|).add hD.integrable.abs) ?_ ?_
    · exact (measurable_const.min measurable_id).aestronglyMeasurable
    · filter_upwards [hD.nonneg] with d hd
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx.le hd)]
      have := min_le_right x d
      simp only [Pi.add_apply, abs_of_nonneg hd, abs_of_pos hx]
      linarith [min_le_left x d]
  have hnn : 0 ≤ᵐ[μ] fun d => min x d := by
    filter_upwards [hD.nonneg] with d hd
    exact le_min hx.le hd
  have hmain : ∫ d, min x d ∂μ = ∫ t in (0 : ℝ)..x, (1 - cdf μ t) := by
    rw [hint.integral_eq_integral_meas_lt hnn]
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi Ioc_subset_Ioi_self]
    · rw [integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le hx.le,
        integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      have : {a : ℝ | t < min x a} = Ioi t := by
        ext a; simp [lt_min_iff, ht.2]
      show μ.real {a : ℝ | t < min x a} = 1 - cdf μ t
      rw [this, cdf_eq_real, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    · apply Eventually.of_forall
      intro t ht
      have htx : x < t := by
        simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at ht
        exact ht.2 ht.1
      have : {a : ℝ | t < min x a} = ∅ := by
        ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact (min_le_left x a).trans htx.le
      rw [this]; simp
  have hFc : Continuous (cdf μ) := hD.continuous_cdf
  have hsub : ∫ t in (0 : ℝ)..x, (1 - cdf μ t) = x - ∫ t in (0 : ℝ)..x, cdf μ t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hFc.intervalIntegrable _ _)]
    simp
  refine ⟨hmain.trans hsub, ?_⟩
  rw [hmain]
  have hconst : ∫ t in (0 : ℝ)..x, (1 - cdf μ x) = x * (1 - cdf μ x) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [← hconst]
  have hF0 := F0 μ hD
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hx
    continuousOn_const ((continuous_const.sub hFc).continuousOn)
  · intro t ht
    have := (cdf μ).mono ht.2
    simp only [Pi.sub_apply]
    linarith
  · refine ⟨0, ⟨le_refl _, hx.le⟩, ?_⟩
    simp only [Pi.sub_apply]
    rw [hF0]
    have hFx : 0 < cdf μ x := by
      by_contra h
      push_neg at h
      have hx0 : cdf μ x = 0 := le_antisymm h (cdf_nonneg μ x)
      have := hD.strictMonoOn_cdf (show (0 : ℝ) ∈ {t | 0 ≤ t ∧ cdf μ t < 1} from ⟨le_refl _, by rw [hF0]; norm_num⟩)
        (show x ∈ {t | 0 ≤ t ∧ cdf μ t < 1} from ⟨hx.le, by rw [hx0]; norm_num⟩) hx
      rw [hF0, hx0] at this
      exact lt_irrefl _ this
    linarith
