-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_tendsto_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:00.527909+00:00
-- url     : https://prove2.me/submissions/9b7c27b6-d337-43cb-b058-ab58e0b8ecea

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollTendstoOfContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise
namespace ReciprocityTheory.L2DbarEstimates.B
theorem _root_.solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι} {K : ι → Kernel E μ}
    (hK : Tendsto (fun i => (K i).r) l (𝓝 0)) {g : E → ℂ} (hgs : HasCompactSupport g)
    (hgc : Continuous g) : Tendsto (fun i => eLpNorm (moll (K i) g - g) 2 μ) l (𝓝 0) := by
  have hgu : UniformContinuous g := hgs.uniformContinuous_of_continuous hgc
  set S := Metric.cthickening 1 (tsupport g) with hS
  have hSc : IsCompact S := hgs.isCompact.cthickening
  set C := μ S ^ ((2 : ℝ≥0∞).toReal⁻¹) with hC
  have hCfin : C ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hSc.measure_lt_top.ne
  have hgm : AEStronglyMeasurable g μ := hgc.aestronglyMeasurable
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, eLpNorm (moll (K i) g - g) 2 μ ≤ C * ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨ρ, hρ, hρg⟩ := Metric.uniformContinuous_iff.1 hgu δ hδ
    filter_upwards [hK.eventually (gt_mem_nhds (lt_min hρ one_pos))] with i hi
    have hr : (K i).r < ρ := lt_of_lt_of_le hi (min_le_left _ _)
    have hr1 : (K i).r < 1 := lt_of_lt_of_le hi (min_le_right _ _)
    have hbound : ∀ x, ‖(moll (K i) g - g) x‖ ≤ δ := by
      intro x
      rw [Pi.sub_apply, ← dist_eq_norm]
      simp only [moll]
      exact dist_convolution_le hδ.le (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
        (fun y hy => (hρg (lt_trans (mem_ball.1 hy) hr)).le)
    have hsupp : Function.support (moll (K i) g - g) ⊆ S := by
      intro x hx
      by_contra hxS
      apply hx
      have hx0 : ∀ y ∈ ball x (K i).r, g y = 0 := by
        intro y hy
        by_contra hy0
        apply hxS
        refine Metric.mem_cthickening_of_dist_le x y 1 _ (subset_tsupport _ hy0) ?_
        rw [dist_comm]; exact le_of_lt (lt_trans (mem_ball.1 hy) hr1)
      have hgx : g x = 0 := hx0 x (mem_ball_self (K i).r_pos)
      have h0 : dist (moll (K i) g x) (0 : ℂ) ≤ 0 := by
        simp only [moll]
        exact dist_convolution_le le_rfl (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
          (fun y hy => by rw [hx0 y hy, dist_self])
      rw [Pi.sub_apply, hgx, sub_zero]
      exact dist_le_zero.1 h0
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    refine (eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hbound)).trans ?_
    rw [Measure.restrict_apply_univ]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨n, hn, hnε⟩ := ENNReal.exists_nnreal_pos_mul_lt hCfin hε.ne'
  filter_upwards [key n (NNReal.coe_pos.2 hn)] with i hi
  refine hi.trans ?_
  rw [ENNReal.ofReal_coe_nnreal, mul_comm]
  exact hnε.le
end ReciprocityTheory.L2DbarEstimates.B
