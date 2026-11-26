-- Prove2me | solution 1 for Sendov.sqrtB_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:02.909905+00:00
-- url     : https://prove2.me/submissions/1e62bff7-bd51-4636-869a-bef6853b4682

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) (hα' : α ≤ 17) : Real.sqrt (α / (3 + α)) ≤ 12 / 13 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hB : α / (3 + α) ≤ 144 / 169 := by
    rw [div_le_div_iff₀ h3 (by norm_num)]
    linarith
  calc Real.sqrt (α / (3 + α)) ≤ Real.sqrt (144 / 169) := Real.sqrt_le_sqrt hB
    _ = 12 / 13 := by
        rw [show (144 : ℝ) / 169 = (12 / 13) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12 / 13)]
end Sendov
