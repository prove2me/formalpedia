-- Prove2me | solution 1 for ThreeSumApsp.isBigOPow_floor_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:14.49954+00:00
-- url     : https://prove2.me/submissions/2d9493ee-7a78-4a4f-8320-6f38de2f1dc7

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
theorem _root_.solution (μ : ℝ) : IsBigOPow (fun n : ℕ => (⌊(n : ℝ) ^ μ⌋₊ : ℝ)) μ := by
  refine .of_abs_le 1 0 fun n _ => ?_
  rw [abs_of_nonneg (Nat.cast_nonneg _), one_mul]
  exact Nat.floor_le (Real.rpow_nonneg n.cast_nonneg μ)
end ThreeSumApsp
