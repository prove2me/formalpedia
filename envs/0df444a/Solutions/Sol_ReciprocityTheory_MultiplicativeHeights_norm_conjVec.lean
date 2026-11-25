-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.norm_conjVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:36.844128+00:00
-- url     : https://prove2.me/submissions/2b9142d9-e160-47b3-8cf7-f9d19b9fe4cf

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB

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
theorem _root_.solution {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : ‖conjVec c‖ = ‖c‖ := by
  simp [conjVec, EuclideanSpace.norm_eq]
end ReciprocityTheory.MultiplicativeHeights
