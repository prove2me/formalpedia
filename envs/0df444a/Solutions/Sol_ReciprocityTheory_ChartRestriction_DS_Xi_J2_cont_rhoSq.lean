-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.cont_rhoSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:36.082478+00:00
-- url     : https://prove2.me/submissions/320d5597-ba2a-4e29-8587-cb5deef9e434

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_lsq

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
theorem _root_.solution {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => rhoSq x l := by
  unfold rhoSq
  refine ((cont_lsq _).add (continuous_finsetSum _ fun j _ => by fun_prop)).add
    (continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop)
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
