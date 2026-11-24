-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.ltLog_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:15.152943+00:00
-- url     : https://prove2.me/submissions/a135901c-1b88-42ab-9ab6-6fd022c85d5a

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
variable {K : Type} [Field K] (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (l : ℕ) (hl : 2 ≤ l) : constantCoeff (ltLog K l) = 0 := by
  first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, dif_neg]
  rintro ⟨j, hj⟩
  have h0 : 0 < (l ^ 2) ^ j := pow_pos (pow_pos (by omega) 2) j
  rw [← hj] at h0
  exact lt_irrefl 0 h0
end ReciprocityTheory.ChartRestriction.L1
