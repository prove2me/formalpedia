-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.leadAt_first_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:55:58.232581+00:00
-- url     : https://prove2.me/submissions/6fc442ca-4566-44b8-948a-3bcbf8a1c6d4

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
theorem _root_.solution {g : PowerSeries K} (hg : IntegralPS g) (h : ∃ i, ‖coeff i g‖ = 1) :
    ∃ i₀, (∀ i, ‖coeff i g‖ = 1 → i₀ ≤ i) ∧ LeadAt g 1 i₀ := by
  classical
  refine ⟨Nat.find h, fun i hi => Nat.find_min' h hi, one_pos, hg,
    fun n hn => lt_of_le_of_ne (hg n) (Nat.find_min h hn), Nat.find_spec h⟩
end ReciprocityTheory.ChartRestriction.L1
