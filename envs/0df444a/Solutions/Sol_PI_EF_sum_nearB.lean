-- Prove2me | solution 1 for PI.EF.sum_nearB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:32.5277+00:00
-- url     : https://prove2.me/submissions/b3a3d360-1531-44f2-903c-84f06df0af94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution (u T : ℝ) :
    ∑ n ∈ range (⌊u⌋₊ + (⌊u⌋₊ + 2)), nearB u T n =
      4 + 2 * ((4 * u / T) * ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1)) := by
  set n0 := ⌊u⌋₊ with hn0
  rw [Finset.sum_range_add, Finset.sum_range_succ', Finset.sum_range_succ']
  have e1 : ∑ n ∈ range n0, nearB u T n = (4 * u / T) * ∑ j ∈ range n0, 1 / ((j : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect (fun j => 1 / ((j : ℝ) + 1)) n0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n < n0 := Finset.mem_range.mp hn
    have hc : ((n0 - 1 - n : ℕ) : ℝ) + 1 = (n0 : ℝ) - n := by
      have : n0 - 1 - n + 1 = n0 - n := by omega
      have h2 : ((n0 - 1 - n + 1 : ℕ) : ℝ) = ((n0 - n : ℕ) : ℝ) := by rw [this]
      rw [Nat.cast_sub hn'.le] at h2
      rw [← h2]
      push_cast
      ring
    unfold nearB
    rw [if_pos (by rw [← hn0]; exact hn'), hc, ← hn0]
    ring
  have e2 : ∑ i ∈ range n0, nearB u T (n0 + (i + 1 + 1)) =
      (4 * u / T) * ∑ j ∈ range n0, 1 / ((j : ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold nearB
    rw [← hn0, if_neg (by omega), if_neg (by omega)]
    have : ((n0 + (i + 1 + 1) : ℕ) : ℝ) - n0 - 1 = (i : ℝ) + 1 := by push_cast; ring
    rw [this]
    ring
  have e3 : nearB u T (n0 + (0 + 1)) = 2 := by
    unfold nearB
    rw [← hn0, if_neg (by omega), if_pos (by omega)]
  have e4 : nearB u T (n0 + 0) = 2 := by
    unfold nearB
    rw [← hn0, if_neg (by omega), if_pos (by omega)]
  rw [e1, e2, e3, e4]
  ring
end PI.EF
