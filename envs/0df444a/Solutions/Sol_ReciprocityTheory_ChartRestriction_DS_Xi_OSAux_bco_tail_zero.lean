-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.bco_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:27:28.536598+00:00
-- url     : https://prove2.me/submissions/233a8379-5a2c-4f38-ae8d-ce126269c0bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (y : Yp p m) : bco (tailPt y) 0 = bco (tailPt y) 1 := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  induction j using Fin.cases with
  | zero => simp [ReciprocityTheory.ChartRestriction.DS.Xi.tailPt]
  | succ k => simp
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
