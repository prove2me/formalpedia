-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.ltLog_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:38:10.985944+00:00
-- url     : https://prove2.me/submissions/ac9b7290-2f37-45bc-851b-57812c68726b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero

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
theorem _root_.solution (l : ℕ) : PowerSeries.map φ (ltLog K l) = ltLog L l := by
  ext n
  first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.L1
