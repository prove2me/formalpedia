-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divBy_iff_mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:45:01.294863+00:00
-- url     : https://prove2.me/submissions/cb2d05fd-c932-4d2d-8e1f-39e3452495ea

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
theorem _root_.solution (x : K) (f : PowerSeries K) : DivBy x f ↔ DivByMv (ι := Unit) x f := by
  unfold DivBy DivByMv
  constructor
  · intro h d
    have hd : d = Finsupp.single () (d ()) := by
      refine Finsupp.ext fun u => ?_
      cases u
      simp
    rw [hd]
    exact h (d ())
  · intro h n
    exact h (Finsupp.single () n)
end ReciprocityTheory.ChartRestriction.L1
