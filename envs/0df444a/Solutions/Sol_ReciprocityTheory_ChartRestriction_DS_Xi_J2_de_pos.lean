-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.de_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:44.138531+00:00
-- url     : https://prove2.me/submissions/caa94f52-ded2-41f8-abf1-5be376d752e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_one_le_lsq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_one_le_rhoSq

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
theorem _root_.solution {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 < de x l := by
  unfold de
  apply Real.sqrt_pos.2
  have h1 := one_le_lsq x l; have h2 := one_le_rhoSq x l
  have : 0 ≤ ‖bco x l‖ ^ 2 := by positivity
  nlinarith
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
