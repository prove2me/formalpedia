-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.cont_de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:23:52.300084+00:00
-- url     : https://prove2.me/submissions/b874a688-8372-4972-aee0-90a5dcb640a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_lsq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_rhoSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_bco

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
theorem _root_.solution {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => de x l :=
  Real.continuous_sqrt.comp (((cont_lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
