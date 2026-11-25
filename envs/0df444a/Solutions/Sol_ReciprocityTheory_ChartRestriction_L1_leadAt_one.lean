-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.leadAt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:44:36.171748+00:00
-- url     : https://prove2.me/submissions/394c4161-9d6f-4f11-8019-f7b53f7aba08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss

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
open Formalism.L2.Th1
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : LeadAt (1 : PowerSeries K) 1 0 := by
  refine ⟨one_pos, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), by simp⟩
  rw [coeff_one]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.L1
