-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dot_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:29.991306+00:00
-- url     : https://prove2.me/submissions/593b7057-78af-4186-ac5b-e1d7f095f7e7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (u v w : Fin n → ℝ) : dot (u - v) w = dot u w - dot v w := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]
end ReciprocityTheory.ChartRestriction.DS
