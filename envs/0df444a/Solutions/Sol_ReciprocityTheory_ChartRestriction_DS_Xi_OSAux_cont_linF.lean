-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.cont_linF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:20.093275+00:00
-- url     : https://prove2.me/submissions/c5721275-367a-4ad1-b17b-71ac48490593

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
theorem _root_.solution {p m : ℕ} (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (linF η η' ζ) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.linF
  exact (continuous_finsetSum _ fun j _ => by fun_prop).add (continuous_finsetSum _ fun i _ => by fun_prop)
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
