-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.blockSphereProb_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:36.541183+00:00
-- url     : https://prove2.me/submissions/c37cd2c9-ea5b-4a60-bf4c-d585df61631e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {B n : ℕ} (hn : 0 < n) :
    MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.blockSphereProb B n) := by
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  haveI : MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.sphereProb n) := by
    unfold ReciprocityTheory.MultiplicativeHeights.sphereProb
    have hne : ∃ x : EuclideanSpace ℂ (Fin n), x ≠ 0 :=
      ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
    have hdim : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr hne
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · rw [MeasureTheory.Measure.toSphere_apply_univ]
      refine mul_ne_zero ?_ (Metric.measure_ball_pos _ _ one_pos).ne'
      exact_mod_cast hdim.ne'
    · rw [MeasureTheory.Measure.toSphere_apply_univ]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (MeasureTheory.measure_ball_lt_top).ne
  infer_instance
end ReciprocityTheory.ChartRestriction.G.T0
