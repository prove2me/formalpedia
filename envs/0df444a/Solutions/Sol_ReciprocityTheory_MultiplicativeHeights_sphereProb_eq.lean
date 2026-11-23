-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sphereProb_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:51.455707+00:00
-- url     : https://prove2.me/submissions/839c62ca-711c-49b8-8050-f18b86f6cf39

import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreD

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
open MeasureTheory Metric Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (n : ℕ) : sphereProb n =
    ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ]
end ReciprocityTheory.MultiplicativeHeights
