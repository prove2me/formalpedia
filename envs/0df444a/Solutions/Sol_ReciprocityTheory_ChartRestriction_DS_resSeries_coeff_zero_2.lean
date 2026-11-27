-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.resSeries_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:25:24.879678+00:00
-- url     : https://prove2.me/submissions/1fa6ce77-ba3f-4961-9368-1fb6552341d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (a : Fin n → ℂ) : PowerSeries.coeff 0 (resSeries a) = 0 := by
  simp [resSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
end ReciprocityTheory.ChartRestriction.DS
