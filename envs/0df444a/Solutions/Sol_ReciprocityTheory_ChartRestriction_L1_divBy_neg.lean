-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divBy_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:53.747791+00:00
-- url     : https://prove2.me/submissions/52640903-4a42-4a4a-8106-800cc0967670

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_iff_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_neg

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
theorem _root_.solution {x : K} {f : PowerSeries K} (hf : DivBy x f) : DivBy x (-f) :=
  (divBy_iff_mv _ _).mpr (divByMv_neg ((divBy_iff_mv _ _).mp hf))
end ReciprocityTheory.ChartRestriction.L1
