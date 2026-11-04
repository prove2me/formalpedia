-- Prove2me | solution 1 for ThreeSumApsp.WordRam.Bounded.abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:04.704197+00:00
-- url     : https://prove2.me/submissions/f7137533-98b9-4385-856f-20afab6aa308

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
namespace Bounded
theorem _root_.solution {Q : EndStatement.Problem} {x : Bounded Q} {a : ℤ} (ha : a ∈ Q.input x.x) :
    |a| ≤ (x.U : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast x.bounded a ha
end Bounded
end ThreeSumApsp.WordRam
