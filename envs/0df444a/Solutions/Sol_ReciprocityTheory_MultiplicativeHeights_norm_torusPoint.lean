-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.norm_torusPoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:20.079882+00:00
-- url     : https://prove2.me/submissions/7c14f301-b704-4220-81e9-95edd51391f5

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB

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
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (θ : ι → ℝ) (j : ι) : ‖torusPoint θ j‖ = 1 := by simp [torusPoint, Complex.norm_exp]
end ReciprocityTheory.MultiplicativeHeights
