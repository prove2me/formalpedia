-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_l2Tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:19.842495+00:00
-- url     : https://prove2.me/submissions/dffb9f63-f942-42ac-8d1d-9314a760db67

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollTendstoOfContinuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_tendsto_of_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_young


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
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : MollifierL2Tendsto E μ ι := by
  intro l K hK u hu
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hη : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by simp)).ne'
  obtain ⟨g, hgs, hug, hgc, hgL⟩ := hu.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hη
  have hmid := moll_tendsto_of_continuous E μ hK hgs hgc
  rw [ENNReal.tendsto_nhds_zero] at hmid
  filter_upwards [hmid (ε / 3) (pos_iff_ne_zero.2 hη)] with i hi
  have hcs : HasCompactSupport (K i).toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) (K i).r) (fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall ((K i).support_subset h)))
  have hKc : Continuous (K i).toFun := (K i).smooth.continuous
  have hug' : MemLp (u - g) 2 μ := hu.sub hgL
  have hli : LocallyIntegrable (u - g) μ := hug'.locallyIntegrable (by norm_num)
  have hgli : LocallyIntegrable g μ := hgL.locallyIntegrable (by norm_num)
  have hlin : moll (K i) u = moll (K i) (u - g) + moll (K i) g := by
    simp only [moll]
    rw [← ConvolutionExists.distrib_add (hcs.convolutionExists_left _ hKc hli)
      (hcs.convolutionExists_left _ hKc hgli), sub_add_cancel]
  have hc1 : Continuous (moll (K i) (u - g)) := hcs.continuous_convolution_left _ hKc hli
  have hc2 : Continuous (moll (K i) g) := hcs.continuous_convolution_left _ hKc hgli
  have hdec : moll (K i) u - u = moll (K i) (u - g) + (moll (K i) g - g) + (g - u) := by
    rw [hlin]; abel
  have hY : eLpNorm (moll (K i) (u - g)) 2 μ ≤ eLpNorm (u - g) 2 μ := by
    have h := moll_young E μ (K i) (u - g) Set.univ MeasurableSet.univ hug'.aestronglyMeasurable
    have hth : thickening (K i).r (Set.univ : Set E) = Set.univ :=
      Set.eq_univ_of_forall fun x => Metric.self_subset_thickening (K i).r_pos _ (Set.mem_univ x)
    simp only [hth, Measure.restrict_univ] at h
    exact h
  rw [hdec]
  calc eLpNorm (moll (K i) (u - g) + (moll (K i) g - g) + (g - u)) 2 μ
      ≤ eLpNorm (moll (K i) (u - g) + (moll (K i) g - g)) 2 μ + eLpNorm (g - u) 2 μ :=
        eLpNorm_add_le (hc1.aestronglyMeasurable.add (hc2.aestronglyMeasurable.sub hgc.aestronglyMeasurable))
          (hgc.aestronglyMeasurable.sub hu.aestronglyMeasurable) (by norm_num)
    _ ≤ eLpNorm (moll (K i) (u - g)) 2 μ + eLpNorm (moll (K i) g - g) 2 μ + eLpNorm (g - u) 2 μ := by
        gcongr
        exact eLpNorm_add_le hc1.aestronglyMeasurable
          (hc2.aestronglyMeasurable.sub hgc.aestronglyMeasurable) (by norm_num)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact hY.trans hug
        · rw [eLpNorm_sub_comm]; exact hug
    _ = ε := ENNReal.add_thirds ε
end ReciprocityTheory.L2DbarEstimates.B
