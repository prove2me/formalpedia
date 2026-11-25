-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:47:23.580037+00:00
-- url     : https://prove2.me/submissions/a5e19e95-85b6-4a03-948b-682860e102f2

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_sphereMap
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_toSphere_map_sphereMap

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
open MeasureTheory Metric
open scoped Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (sphereMap U) (sphereProb n) (sphereProb n) := by
  refine ⟨(continuous_sphereMap U).measurable, ?_⟩
  unfold sphereProb ProbabilityTheory.cond
  rw [Measure.restrict_univ, Measure.map_smul, toSphere_map_sphereMap]
end ReciprocityTheory.MultiplicativeHeights
