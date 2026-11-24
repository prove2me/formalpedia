-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.gauss_norm_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:55:56.621819+00:00
-- url     : https://prove2.me/submissions/165bdbc9-ff10-4489-b1e0-90c6958649d6

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
theorem _root_.solution {α : Type} (s : Finset α) (f : α → K) {r : ℝ} (hr : 0 < r)
    (h : ∀ a ∈ s, ‖f a‖ < r) : ‖∑ a ∈ s, f a‖ < r := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hr
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    exact hle.trans_lt (h i hi)
end ReciprocityTheory.ChartRestriction.L1
