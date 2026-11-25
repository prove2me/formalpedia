-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.upd_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:31.84381+00:00
-- url     : https://prove2.me/submissions/ceedf6a4-f8bc-403d-aa39-459ee49c78b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailFinOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p : ℕ} (ν : Fin (p + 2) → ℝ) :
    Function.update (Fin.tail ν) 0 (ν 0 + Fin.tail ν 0) = fun j => ν j.succ + if j = 0 then ν 0 else 0 := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [Fin.tail, add_comm]
  · simp [Fin.tail]
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
