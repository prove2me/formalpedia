-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.resid_poleVd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:04.517459+00:00
-- url     : https://prove2.me/submissions/30753be7-4a62-42e9-b39f-3d9595cc3899

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue

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
theorem _root_.solution (μ : Fin n → ℝ) (s : Fin n) : resid (poleVd μ) s = ((ratioVd μ s : ℝ) : ℂ) := by
  simp only [resid, ratioVd, poleVd]
  push_cast
  refine Finset.prod_congr rfl fun s' _ => ?_
  rw [← neg_div_neg_eq]
  ring
end ReciprocityTheory.ChartRestriction.DS
