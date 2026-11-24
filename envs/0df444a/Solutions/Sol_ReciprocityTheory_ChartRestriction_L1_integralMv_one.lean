-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralMv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:57:00.367822+00:00
-- url     : https://prove2.me/submissions/6d20b1a6-ded0-490e-99e7-ad7970cc3521

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one

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
theorem _root_.solution : IntegralMv (1 : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.L1
