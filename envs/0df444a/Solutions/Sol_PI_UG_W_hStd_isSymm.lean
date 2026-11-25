-- Prove2me | solution 1 for PI.UG.W.hStd_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:32:25.371609+00:00
-- url     : https://prove2.me/submissions/bf54c1cf-1371-47c8-bb82-99dda1adf292

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan
import Theorems.Thm_PI_UG_W_hStd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W
namespace PI.UG.W
theorem _root_.solution (E : Type) [Field E] [StarRing E] (n : ℕ) : (hStd E n).IsSymm := by
  refine LinearMap.isSymm_def.mpr fun x y => ?_
  rw [hStd_apply, hStd_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply, star_mul, star_star, mul_comm]
end PI.UG.W
