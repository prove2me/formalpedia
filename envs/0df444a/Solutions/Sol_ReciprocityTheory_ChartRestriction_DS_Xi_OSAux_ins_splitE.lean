-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.ins_splitE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:02.488271+00:00
-- url     : https://prove2.me/submissions/1b53efb8-7662-411a-8f0e-d66f960553ab

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
theorem _root_.solution {p m : ℕ} (x : Xp (p + 1) m) : ins (splitE p m x).1 (splitE p m x).2 = x := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ k =>
    show x.2.1 (Fin.succAbove 0 k) = x.2.1 k.succ
    simp
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
