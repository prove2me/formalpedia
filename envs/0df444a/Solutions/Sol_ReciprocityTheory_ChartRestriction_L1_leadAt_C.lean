-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.leadAt_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:55:57.271528+00:00
-- url     : https://prove2.me/submissions/0f8a4c5b-b476-4abe-ab2e-151c2bc5798f

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
theorem _root_.solution {c : K} (hc : c ≠ 0) : LeadAt (C c : PowerSeries K) ‖c‖ 0 := by
  refine ⟨norm_pos_iff.mpr hc, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), by simp⟩
  rw [coeff_C]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.L1
