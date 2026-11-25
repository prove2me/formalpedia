-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.cont_de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:50.649636+00:00
-- url     : https://prove2.me/submissions/a600272f-1fc1-487f-8c8d-758f3f50d197

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_cont_Lsq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_cont_rhoSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_cont_bco

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
theorem _root_.solution {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  exact Real.continuous_sqrt.comp
    (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
