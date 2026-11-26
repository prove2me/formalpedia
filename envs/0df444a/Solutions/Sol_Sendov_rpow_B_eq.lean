-- Prove2me | solution 1 for Sendov.rpow_B_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:51:25.376036+00:00
-- url     : https://prove2.me/submissions/6e8f65ac-69fb-436d-b68a-6845e4073f6c

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 4 ≤ n) (hα : 0 ≤ α) :
    (α / (3 + α)) ^ (((n : ℝ) - 4) / 2) = Real.sqrt (α / (3 + α)) ^ (n - 4) := by
  have hB : (0 : ℝ) ≤ α / (3 + α) := div_nonneg hα (by linarith)
  have hcast : ((n - 4 : ℕ) : ℝ) = (n : ℝ) - 4 := by
    push_cast [Nat.cast_sub hn]
    ring
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((α / (3 + α)) ^ ((1 : ℝ) / 2)) (n - 4),
    ← Real.rpow_mul hB, hcast]
  congr 1
  ring
end Sendov
