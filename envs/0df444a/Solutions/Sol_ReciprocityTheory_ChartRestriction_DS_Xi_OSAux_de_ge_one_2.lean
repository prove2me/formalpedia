-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:15.849046+00:00
-- url     : https://prove2.me/submissions/35e763ff-6f3c-469c-9687-025c1c429508

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_ge_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_rhoSq_ge

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
theorem _root_.solution {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ de x l := by
  have hL := Lsq_ge_one x l
  have hR : 1 ≤ ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq x l := le_trans hL (rhoSq_ge x l l)
  have hc : 0 ≤ ‖ReciprocityTheory.ChartRestriction.DS.Xi.bco x l‖ ^ 2 := by positivity
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
