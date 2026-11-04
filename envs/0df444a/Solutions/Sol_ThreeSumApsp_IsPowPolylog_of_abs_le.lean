-- Prove2me | solution 1 for ThreeSumApsp.IsPowPolylog.of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:51.626971+00:00
-- url     : https://prove2.me/submissions/b03c229a-ab7c-4971-8285-d557c2bf7638

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_isBigO_of_abs_le


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsPowPolylog
namespace ThreeSumApsp.IsPowPolylog
theorem _root_.solution (C : ℝ) (e n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → |f n| ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)) : IsPowPolylog f a :=
  ⟨e, isBigO_of_abs_le C n₀ h⟩
end ThreeSumApsp.IsPowPolylog
