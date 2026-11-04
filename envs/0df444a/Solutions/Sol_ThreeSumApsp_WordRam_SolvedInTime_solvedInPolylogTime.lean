-- Prove2me | solution 1 for ThreeSumApsp.WordRam.SolvedInTime.solvedInPolylogTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:00:25.82745+00:00
-- url     : https://prove2.me/submissions/b56751af-178b-4eb6-b29d-1759a5a7c2f9

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter
namespace ThreeSumApsp.WordRam
namespace SolvedInTime
theorem _root_.solution {Q : EndStatement.Problem} {a : ℝ} {e : ℕ}
    (h : SolvedInTime Q a e) : SolvedInPolylogTime Q a :=
  fun κ => ⟨e, h κ⟩
end SolvedInTime
end ThreeSumApsp.WordRam
