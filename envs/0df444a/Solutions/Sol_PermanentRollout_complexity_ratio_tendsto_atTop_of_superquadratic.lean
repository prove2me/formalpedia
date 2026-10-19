-- Prove2me | solution 1 for PermanentRollout.complexity_ratio_tendsto_atTop_of_superquadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/44f85c3d-19ce-405f-add4-9fddc11b8a4b

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution
    (complexity : ℕ → ℕ)
    (bound : ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (n : ℝ) ^ 2 ≤ (complexity n : ℝ)) :
    Filter.Tendsto
      (fun n : ℕ => (complexity n : ℝ) / (n : ℝ) ^ 2)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.2
  intro C
  have hpositive : 0 < max C 1 := lt_max_of_lt_right (by norm_num)
  obtain ⟨N, hN⟩ := bound (max C 1) hpositive
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn_positive : 0 < (n : ℝ) := by
    exact_mod_cast (le_trans (le_max_right _ _) hn : 1 ≤ n)
  apply (le_div_iff₀ (sq_pos_of_pos hn_positive)).2
  exact le_trans
    (mul_le_mul_of_nonneg_right (le_max_left C 1) (sq_nonneg (n : ℝ)))
    (hN n (le_trans (le_max_left _ _) hn))
end PermanentRollout
