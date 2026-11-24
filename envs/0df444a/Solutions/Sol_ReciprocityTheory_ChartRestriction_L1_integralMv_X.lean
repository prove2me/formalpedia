-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralMv_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:10.179287+00:00
-- url     : https://prove2.me/submissions/75383d74-b407-43a8-a7cf-cbcfe6be4607

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
theorem _root_.solution (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.L1
