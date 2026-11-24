-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralMv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:29.374523+00:00
-- url     : https://prove2.me/submissions/aa3652a5-e46e-43bb-8dcd-9368c7262a6a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_mul

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {ι : Type}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {F : MvPowerSeries ι K} (hF : IntegralMv F) (n : ℕ) : IntegralMv (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact integralMv_one
  | succ n ih => rw [pow_succ]; exact integralMv_mul ih hF
end ReciprocityTheory.ChartRestriction.L1
