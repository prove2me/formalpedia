-- Prove2me | solution 1 for ThreeSumApsp.isBigOPow_inv_floor_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:48.810844+00:00
-- url     : https://prove2.me/submissions/10cc5bf5-fa56-43b2-a309-380745ea2271

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
theorem _root_.solution {μ : ℝ} (hμ : 0 ≤ μ) :
    IsBigOPow (fun n : ℕ => (⌊(n : ℝ) ^ μ⌋₊ : ℝ)⁻¹) (-μ) := by
  refine .of_abs_le 2 1 fun n hn => ?_
  have hone : 1 ≤ (n : ℝ) ^ μ := Real.one_le_rpow (Nat.one_le_cast.2 hn) hμ
  have hfloor : (1 : ℝ) ≤ ⌊(n : ℝ) ^ μ⌋₊ := Nat.one_le_cast.2 (Nat.floor_pos.2 hone)
  have hlt : (n : ℝ) ^ μ < ⌊(n : ℝ) ^ μ⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)), Real.rpow_neg n.cast_nonneg,
    ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
  linarith
end ThreeSumApsp
