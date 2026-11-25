-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.wpNum_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:17:20.58918+00:00
-- url     : https://prove2.me/submissions/47bc529f-481b-4fca-8caf-17f23d685212

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
theorem _root_.solution : PowerSeries.map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) := by
  ext n
  unfold wpNum
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp [cW_map]
end ReciprocityTheory.ChartRestriction.L1
