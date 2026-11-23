-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sphereMeasure_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:23.188813+00:00
-- url     : https://prove2.me/submissions/2bfdf797-a4f7-4d8e-9b97-103576a5d47c

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (sphereProb n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold sphereProb
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ (Metric.measure_ball_pos _ _ one_pos).ne'
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℂ (Fin n))).ne'
  · rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
end ReciprocityTheory.MultiplicativeHeights
