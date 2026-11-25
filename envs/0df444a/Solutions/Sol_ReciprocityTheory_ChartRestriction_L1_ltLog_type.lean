-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.ltLog_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:57:18.371873+00:00
-- url     : https://prove2.me/submissions/017d1d38-7e49-47b2-8106-ab250a8300bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ltLog_sub_eq_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_X


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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : 2 ≤ l) (τ : K →+* K) : IsFunEqType l (l ^ 2) τ (ltLog K l) := by
  unfold IsFunEqType
  rw [ltLog_sub_eq_X hl τ]
  exact integralPS_X
end ReciprocityTheory.ChartRestriction.L1
