-- Prove2me | solution 1 for ThreeSumApsp.IsPowPolylog.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:19.151643+00:00
-- url     : https://prove2.me/submissions/509e038a-e5a3-458f-ba50-aff07319e0cf

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_of_isBigO
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_add
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_rpow__dbdce0
import Theorems.Thm_ThreeSumApsp_IsBigOPow_pow
import Theorems.Thm_ThreeSumApsp_IsBigOPow_isPowPolylog
import Theorems.Thm_ThreeSumApsp_isPowPolylog_const
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_of_isBigO
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_add
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_pow
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_rpow
import Theorems.Thm_ThreeSumApsp_IsBigOPow_isPowPolylog_log_natCast
import Theorems.Thm_ThreeSumApsp_Dominated_add
import Theorems.Thm_ThreeSumApsp_Dominated_mul
import Theorems.Thm_ThreeSumApsp_Dominated_pow
import Theorems.Thm_ThreeSumApsp_isBigO_comp_add_one


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
namespace IsPowPolylog
theorem _root_.solution {G : ℕ → ℝ} {size : ℕ → ℕ} {μ : ℝ} (hG : IsPowPolylog G a)
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) :
    IsPowPolylog (fun n => G (size n)) (a * μ) := by
  obtain ⟨e, hG⟩ := hG
  have hmain := (hsize.rpow ha).isPowPolylog.mul (hsize.isPowPolylog_log_natCast.pow e)
  rw [zero_mul, add_zero, mul_comm μ a] at hmain
  exact (hmain.add ((isPowPolylog_const 1).mono (mul_nonneg ha hμ))).of_isBigO
    (isBigO_comp_add_one hG (fun s => mul_nonneg (Real.rpow_nonneg s.cast_nonneg a)
      (pow_nonneg (Real.log_natCast_nonneg s) e)) size)
end IsPowPolylog
end ThreeSumApsp
