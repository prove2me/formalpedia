-- Prove2me | solution 1 for PermanentRollout.exists_eventual_source_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/e49fa15c-9ba3-4cbb-b102-958e4eea3c6e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_le_two_mul_blockColumns
import Theorems.Thm_PermanentRollout_eight_le_blockVariables

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {d : ℕ} (hd : 3 ≤ d) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      6 * blockWidth d ≤ n ∧
      8 * powerSumParameter d ≤ n * blockWidth d ∧
      4 * powerSumParameter d ≤ blockWidth d * blockColumns n d ∧
      8 ≤ blockVariables n d := by
  refine ⟨max (6 * blockWidth d) (8 * powerSumParameter d), ?_⟩
  intro n hn
  have hlarge : 6 * blockWidth d ≤ n := le_trans (le_max_left _ _) hn
  have hrho : 8 * powerSumParameter d ≤ n := le_trans (le_max_right _ _) hn
  have hwidth : 1 ≤ blockWidth d := by
    simp only [blockWidth]
    omega
  have hwidth_n : n ≤ n * blockWidth d := by
    simpa using Nat.mul_le_mul_left n hwidth
  have hcolumns := le_two_mul_blockColumns n d
  have hrho_columns : 4 * powerSumParameter d ≤ blockColumns n d := by
    omega
  have hscale : 4 * powerSumParameter d ≤ blockWidth d * blockColumns n d := by
    calc
      4 * powerSumParameter d ≤ blockColumns n d := hrho_columns
      _ ≤ blockWidth d * blockColumns n d := by
        simpa [mul_comm] using Nat.mul_le_mul_right (blockColumns n d) hwidth
  exact ⟨hlarge, le_trans hrho hwidth_n, hscale,
    eight_le_blockVariables hd hlarge⟩
end PermanentRollout
