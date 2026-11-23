-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.isProbabilityMeasure_sphereProb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:49.493872+00:00
-- url     : https://prove2.me/submissions/4aacdfb6-dda5-4487-b6d8-5f023c852736

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
private theorem toSphere_univ_ne_zero_of_pos {n : ℕ} (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
  have : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    ⟨⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℂ), 0, fun h => by
        simpa using congrArg norm h⟩⟩
  rw [Measure.toSphere_apply_univ]
  refine mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'
  exact_mod_cast (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℂ (Fin n))).ne'
private theorem toSphere_univ_ne_top' {n : ℕ} :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
  exact measure_ne_top _ _
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (sphereProb n) := by
  constructor
  simp only [sphereProb, ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (toSphere_univ_ne_zero_of_pos hn) toSphere_univ_ne_top'
end ReciprocityTheory.MultiplicativeHeights
