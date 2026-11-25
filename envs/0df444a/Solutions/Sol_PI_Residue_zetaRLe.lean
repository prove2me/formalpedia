-- Prove2me | solution 1 for PI.Residue.zetaRLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:19:21.634429+00:00
-- url     : https://prove2.me/submissions/213ceb4d-eca5-4cff-9ae3-bd8af75a8516

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_SumRangeLe
import Theorems.Thm_PI_Residue_sum_range_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open MeasureTheory intervalIntegral
namespace PI.Residue
theorem _root_.solution : ZetaRLe := by
  intro s hs
  unfold zetaR
  have hpos : 0 < s - 1 := by linarith
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro n
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    | succ N =>
      rw [Finset.sum_range_succ']
      have := sum_range_le s hs N
      have e : ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) + 1) ^ (-s)
          = ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [add_comm]
      rw [e]
      simp only [Nat.cast_zero, zero_add, Real.one_rpow]
      linarith
end PI.Residue
