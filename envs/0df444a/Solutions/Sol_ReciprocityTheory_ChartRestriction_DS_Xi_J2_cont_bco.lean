-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.cont_bco
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:32.523957+00:00
-- url     : https://prove2.me/submissions/733e89ac-c3af-416b-b1f7-527fa5144d0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => bco x l := by
  unfold bco
  refine Continuous.sub ?_ (continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop)
  fun_prop
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
