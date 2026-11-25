-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereRot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:47.183394+00:00
-- url     : https://prove2.me/submissions/949bd9af-4110-4606-aff6-c668fb54f632

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_toSphere_isometry
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
private theorem measurePreserving_sphereProb_of_toSphere {n : ℕ} {f : UnitSphereC n → UnitSphereC n}
    (hf : MeasurePreserving f (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere) :
    MeasurePreserving f (sphereProb n) (sphereProb n) := by
  refine ⟨hf.measurable, ?_⟩
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ]
  rw [Measure.map_smul, hf.map_eq]
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (u : Fin n → Circle) :
    MeasurePreserving (sphereRot u) (sphereProb n) (sphereProb n) :=
  measurePreserving_sphereProb_of_toSphere (f := sphereRot u)
    (measurePreserving_toSphere_isometry (rotLIE u))
end ReciprocityTheory.MultiplicativeHeights
