-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divBy_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:49.451157+00:00
-- url     : https://prove2.me/submissions/6a982863-4827-4285-9f3d-a618fc7eeb37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_iff_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_mul_left

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
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : K} {f g : PowerSeries K} (hf : IntegralPS f) (hg : DivBy x g) :
    DivBy x (f * g) :=
  (divBy_iff_mv _ _).mpr (divByMv_mul_left ((integralPS_iff_mv _).mp hf) ((divBy_iff_mv _ _).mp hg))
end ReciprocityTheory.ChartRestriction.L1
