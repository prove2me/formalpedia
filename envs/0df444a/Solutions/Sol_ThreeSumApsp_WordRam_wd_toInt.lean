-- Prove2me | solution 1 for ThreeSumApsp.WordRam.wd_toInt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:43.632899+00:00
-- url     : https://prove2.me/submissions/3a91ceec-7d99-4f02-aaa3-b6a76f7286b7

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
namespace ThreeSumApsp.WordRam
theorem _root_.solution (w : BitVec W) : wd W w.toInt = w := BitVec.ofInt_toInt
end ThreeSumApsp.WordRam
