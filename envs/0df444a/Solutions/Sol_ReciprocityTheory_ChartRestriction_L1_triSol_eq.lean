-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.triSol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:49.390427+00:00
-- url     : https://prove2.me/submissions/ebf7b2f6-b342-4f39-a7d6-81859d1ba1a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG

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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) (ha : ∀ m, a m m ≠ 0)
    (m : ℕ) : ∑ i ∈ Finset.range (m + 1), triSol a b i * a i m = b m := by
  have h : triSol a b m = (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m := by
    rw [triSol]
  rw [Finset.sum_range_succ, Finset.sum_range, h, div_mul_cancel₀ _ (ha m)]
  ring
end ReciprocityTheory.ChartRestriction.L1
