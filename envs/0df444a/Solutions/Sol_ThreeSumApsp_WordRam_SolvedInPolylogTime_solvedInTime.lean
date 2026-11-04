-- Prove2me | solution 1 for ThreeSumApsp.WordRam.SolvedInPolylogTime.solvedInTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:45.800047+00:00
-- url     : https://prove2.me/submissions/c1a19bd6-c772-4bc3-b74d-e483fb713031

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTimeAt_of_eventually_le
import Theorems.Thm_ThreeSumApsp_eventually_mul_rpow_mul_log_pow_le


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter
namespace ThreeSumApsp.WordRam
namespace SolvedInPolylogTime
theorem _root_.solution {Q : EndStatement.Problem} {a a' : ℝ}
    (h : SolvedInPolylogTime Q a) (ha : a < a') : SolvedInTime Q a' 0 := fun κ =>
  let ⟨e, he⟩ := h κ
  he.of_eventually_le (C := 1) <| by
    simpa only [one_mul, pow_zero, mul_one] using eventually_mul_rpow_mul_log_pow_le 1 ha e
end SolvedInPolylogTime
end ThreeSumApsp.WordRam
