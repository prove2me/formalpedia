-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralPS_iff_mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:01.300691+00:00
-- url     : https://prove2.me/submissions/a8ae2a04-d182-4546-9bb5-6f9a866d173c

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
theorem _root_.solution (f : PowerSeries K) : IntegralPS f ↔ IntegralMv (ι := Unit) f := by
  rw [integralMv_iff_divBy_one]
  unfold IntegralPS DivByMv
  constructor
  · intro h d
    have hd : d = Finsupp.single () (d ()) := by
      refine Finsupp.ext fun u => ?_
      cases u
      simp
    rw [hd, norm_one]
    exact h (d ())
  · intro h n
    have := h (Finsupp.single () n)
    rw [norm_one] at this
    exact this
end ReciprocityTheory.ChartRestriction.L1
