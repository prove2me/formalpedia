-- Prove2me | solution 1 for SubsetShrink.L1.sorted_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:01:03.948883+00:00
-- url     : https://prove2.me/submissions/c01b5c42-71d2-483c-81f0-410dab5efd10

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

set_option autoImplicit false
open SubsetShrink.L1

theorem solution {p : ℕ} (hp : 1 ≤ p) (u : Fin p → ℝ) :
    SubsetShrink.Events.sortedSum u ≤ Real.sqrt (Real.log (2 * (p : ℝ))) * SubsetShrink.Events.l1 u := by
  unfold SubsetShrink.Events.sortedSum
  apply Finset.sup'_le
  intro π _
  have hl1 : SubsetShrink.Events.l1 u = ∑ j : Fin p, |u (π j)| := by
    unfold SubsetShrink.Events.l1
    exact (Equiv.sum_comp π (fun i => |u i|)).symm
  rw [hl1, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hj : (1:ℝ) ≤ (j.val : ℝ) + 1 := by linarith [(Nat.cast_nonneg j.val : (0:ℝ) ≤ j.val)]
  have hs : Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))) ≤ Real.sqrt (Real.log (2 * (p : ℝ))) := by
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log
    · apply div_pos (by linarith) (by linarith)
    · rw [div_le_iff₀ (by linarith)]
      nlinarith
  have := mul_le_mul_of_nonneg_right hs (abs_nonneg (u (π j)))
  linarith
