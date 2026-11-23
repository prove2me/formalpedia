-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.numRho_cardR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:56.943799+00:00
-- url     : https://prove2.me/submissions/029ce8fc-c4e7-4245-9d4f-629a3001a4cd

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
theorem _root_.solution (p : Fin n → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) = ∑ c, if p c then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
end ReciprocityTheory.ChartRestriction.DS
