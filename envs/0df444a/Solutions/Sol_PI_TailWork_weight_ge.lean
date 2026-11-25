-- Prove2me | solution 1 for PI.TailWork.weight_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:42.24067+00:00
-- url     : https://prove2.me/submissions/47ab3233-808b-4584-9454-d13255202cc8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution (k p : ℕ) (hk : 1 ≤ k) (hp : 2 * k + 1 ≤ p) (hodd : p % 2 = 1) :
    (3 - 1 / (2 * (k : ℝ) + 1)) / (p : ℝ) ^ 2 ≤ g ((p + 1) / 2) - g p := by
  obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 := ⟨p / 2, by omega⟩
  have hq : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  rw [hq]
  have hjk : k ≤ j := by omega
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (k : ℝ) ≤ j := by exact_mod_cast hjk
  have hj1 : (1 : ℝ) ≤ j := le_trans hk' hj'
  unfold g
  push_cast
  simp only [add_sub_cancel_right]
  have hmid : 3 - 1 / (2 * (k : ℝ) + 1) ≤ 3 - 1 / (2 * (j : ℝ) + 1) := by
    have : 1 / (2 * (j : ℝ) + 1) ≤ 1 / (2 * (k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have key : 1 / (((j : ℝ) + 1) * j) - 1 / ((2 * (j : ℝ) + 1) * (2 * j))
      - (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2
      = (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1))) := by
    have : (j : ℝ) ≠ 0 := by linarith
    have : (j : ℝ) + 1 ≠ 0 := by linarith
    have : 2 * (j : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  have hpos : 0 ≤ (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1))) := by positivity
  have hstep : (3 - 1 / (2 * (k : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2
      ≤ (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2 :=
    div_le_div_of_nonneg_right hmid (by positivity)
  linarith
end PI.TailWork
