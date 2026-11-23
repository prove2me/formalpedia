-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.continuous_spherePoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:23.223233+00:00
-- url     : https://prove2.me/submissions/b3b585e8-613e-453e-a744-795a3030ee25

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA

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
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (n : ℕ) : Continuous (spherePoint : UnitSphereC n → Fin n → ℂ) := by
  unfold spherePoint
  fun_prop
end ReciprocityTheory.MultiplicativeHeights
