-- Prove2me | solution 1 for ThreeSumApsp.WordRam.SolvedInTime.mono_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:25.537817+00:00
-- url     : https://prove2.me/submissions/3c57f8b7-d2b0-4f17-a7ab-676a36777e4f

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Theorems.Thm_ThreeSumApsp_WordRam_Solves_mono
import Theorems.Thm_ThreeSumApsp_WordRam_IsDataStructure_mono
import Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTimeAt_of_eventually_le

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter
namespace ThreeSumApsp.WordRam
namespace SolvedInTime
theorem _root_.solution {Q : EndStatement.Problem} {a a' : ℝ} {e : ℕ}
    (h : SolvedInTime Q a e) (ha : a ≤ a') : SolvedInTime Q a' e := fun κ =>
  (h κ).of_eventually_le (C := 1) <| (eventually_ge_atTop 1).mono fun n hn =>
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) ha)
      (by positivity)).trans_eq (one_mul _).symm
end SolvedInTime
end ThreeSumApsp.WordRam
