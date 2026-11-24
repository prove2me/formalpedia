-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralMv_iff_divBy_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:46:05.669006+00:00
-- url     : https://prove2.me/submissions/5cd7d73e-ecba-4212-b662-ebd79331ecf5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic

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
theorem _root_.solution (F : MvPowerSeries ι K) : IntegralMv F ↔ DivByMv (1 : K) F := by
  first
  | exact Iff.rfl
  | (unfold IntegralMv DivByMv; simp)
  | simp [IntegralMv, DivByMv]
end ReciprocityTheory.ChartRestriction.L1
