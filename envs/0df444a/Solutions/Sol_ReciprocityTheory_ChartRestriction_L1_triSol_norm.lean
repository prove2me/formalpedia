-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.triSol_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:56.419297+00:00
-- url     : https://prove2.me/submissions/215a9d06-1dee-4ac7-8fef-126c5e2142b7

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
theorem _root_.solution (a : ℕ → ℕ → K) (b : ℕ → K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (r : ℝ) (hb : ∀ m, ‖b m‖ ≤ r) (m : ℕ) : ‖triSol a b m‖ ≤ r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans (hb 0)
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [triSol, norm_div, ha, div_one, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hb m) ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun i _ => ?_
    rw [norm_mul]
    calc ‖triSol a b i.1‖ * ‖a i.1 m‖ ≤ r * 1 :=
          mul_le_mul (ih i.1 i.2) (ha1 _ _) (norm_nonneg _) hr
      _ = r := mul_one r
end ReciprocityTheory.ChartRestriction.L1
