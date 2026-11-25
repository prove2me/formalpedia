-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carU_nsq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:47.768212+00:00
-- url     : https://prove2.me/submissions/8a132d19-75e9-4e31-895b-07970cd44007

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  unfold nsq dot
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]; ring
end ReciprocityTheory.ChartRestriction.DS
