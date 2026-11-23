-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lowK_add_rhoC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:54.937224+00:00
-- url     : https://prove2.me/submissions/2cecb58b-dcab-4356-93d7-12d9fb667b3a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho

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
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (lam : Fin n → ℝ) : lowK ε lam + rhoC ε = lam + rhoN ε := by
  simp only [lowK, sub_add_cancel]
end ReciprocityTheory.ChartRestriction.DS
