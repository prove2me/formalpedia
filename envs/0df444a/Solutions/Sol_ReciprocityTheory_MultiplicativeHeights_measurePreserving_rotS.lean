-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurePreserving_rotS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:11:20.433558+00:00
-- url     : https://prove2.me/submissions/4899ad27-03e2-4750-84cd-58b1fb6e3086

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_sphereMap

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
theorem _root_.solution {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    MeasurePreserving (rotS hu θ) (sphereProb n) (sphereProb n) :=
  measurePreserving_sphereMap _
end ReciprocityTheory.MultiplicativeHeights
