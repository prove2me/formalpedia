-- Prove2me | solution 1 for PermanentFormulaLowerBound.five_le_clog_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/9abb37b8-1da0-468d-805a-cfaeeb3800f4

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {n : ℕ} (hn : 32 ≤ n) :
    5 ≤ Nat.clog 2 n := by
  calc
    5 = Nat.clog 2 (2 ^ 5) :=
      (Nat.clog_pow 2 5 (by norm_num)).symm
    _ ≤ Nat.clog 2 n := Nat.clog_mono_right 2 (by simpa using hn)
end PermanentFormulaLowerBound
