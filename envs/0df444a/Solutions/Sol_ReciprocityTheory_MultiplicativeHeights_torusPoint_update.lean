-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.torusPoint_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:23.183961+00:00
-- url     : https://prove2.me/submissions/320e34e9-7ad4-40fe-a820-6d45a500600d

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
theorem _root_.solution (θ : ι → ℝ) (i : ι) (t : ℝ) :
    torusPoint (update θ i t) = update (torusPoint θ) i (circPt t) := by
  funext j
  by_cases h : j = i
  · subst h; simp [torusPoint, circPt]
  · simp [torusPoint, Function.update_of_ne h]
end ReciprocityTheory.MultiplicativeHeights
