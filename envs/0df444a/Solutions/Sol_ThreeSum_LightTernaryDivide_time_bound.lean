-- Prove2me | solution 1 for ThreeSum.LightTernaryDivide.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:34.187389+00:00
-- url     : https://prove2.me/submissions/e0004b57-6755-46e4-bf4e-f27622f5fbd0

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Mathlib.Data.Int.Order.Lemmas
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryDivide
theorem _root_.solution (V : ℕ) : time V ≤ 200*(Nat.log 2 (V+1)+2) := by
  unfold time LightOutputDecodeDivide.budget
  omega
end ThreeSum.LightTernaryDivide
