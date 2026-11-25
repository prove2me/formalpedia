-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.triIter_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:48:13.726537+00:00
-- url     : https://prove2.me/submissions/d6e7d0c2-676c-48cb-af03-639c37b595cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_triSol_norm

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
theorem _root_.solution (a : ℕ → ℕ → K) (π : K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (k m : ℕ) : ‖triIter a π k m‖ ≤ ‖π‖ ^ k := by
  induction k generalizing m with
  | zero =>
    rw [triIter, pow_zero]
    refine triSol_norm a _ ha1 ha 1 (fun j => ?_) m
    split_ifs
    · exact ha1 0 0
    · simp
  | succ k ih =>
    rw [triIter]
    refine triSol_norm a _ ha1 ha _ (fun j => ?_) m
    split_ifs
    · simp
    · rw [norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _)
end ReciprocityTheory.ChartRestriction.L1
