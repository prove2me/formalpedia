-- Prove2me | solution 1 for ThreeSumApsp.isBigOPow_inv_ceil_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:47.438391+00:00
-- url     : https://prove2.me/submissions/c71f6224-670c-4fd4-9632-64665749b12a

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_of_abs_le

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
theorem _root_.solution (μ : ℝ) : IsBigOPow (fun n : ℕ => (⌈(n : ℝ) ^ μ⌉₊ : ℝ)⁻¹) (-μ) := by
  refine .of_abs_le 1 1 fun n hn => ?_
  have hpos : 0 < (n : ℝ) ^ μ := Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) μ
  rw [abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)), one_mul, Real.rpow_neg n.cast_nonneg]
  exact inv_anti₀ hpos (Nat.le_ceil _)
end ThreeSumApsp
