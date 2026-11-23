-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.de_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:54.028963+00:00
-- url     : https://prove2.me/submissions/80788afe-f527-4351-a348-c016b136f195

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_one_le_lsq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_rhoSq_nonneg

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
theorem _root_.solution {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    de x l ^ 2 = Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2 := by
  unfold de
  rw [Real.sq_sqrt]
  have := one_le_lsq x l; have := rhoSq_nonneg x l
  positivity
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
