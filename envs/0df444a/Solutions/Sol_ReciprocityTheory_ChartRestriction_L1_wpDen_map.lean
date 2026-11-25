-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.wpDen_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:52.907992+00:00
-- url     : https://prove2.me/submissions/6837ba6a-ae8d-4c75-9654-3d9b1b13de09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_cW_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : PowerSeries.map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) := by
  ext n
  unfold wpDen
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp [cW_map]
end ReciprocityTheory.ChartRestriction.L1
