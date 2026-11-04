-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:49.93478+00:00
-- url     : https://prove2.me/submissions/dd65b18a-e542-43ba-9e66-d29df8f83dba

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_isBigOPow_const
import Theorems.Thm_ThreeSumApsp_IsBigOPow_of_isBigO
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_add
import Theorems.Thm_ThreeSumApsp_IsBigOPow_rpow__dbdce0
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_of_isBigO
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_add
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_rpow
import Theorems.Thm_ThreeSumApsp_Dominated_add
import Theorems.Thm_ThreeSumApsp_isBigO_comp_add_one


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
namespace IsBigOPow
theorem _root_.solution {G : ℕ → ℝ} {size : ℕ → ℕ} {μ : ℝ} (hG : IsBigOPow G a)
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) :
    IsBigOPow (fun n => G (size n)) (a * μ) := by
  have hmodel : IsBigOPow (fun n => (size n : ℝ) ^ a + 1) (a * μ) :=
    ((hsize.rpow ha).mono (mul_comm μ a).le).add ((isBigOPow_const 1).mono (mul_nonneg ha hμ))
  exact hmodel.of_isBigO
    (isBigO_comp_add_one hG (fun s => Real.rpow_nonneg s.cast_nonneg a) size)
end IsBigOPow
end ThreeSumApsp
