-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingJacobianWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/26d13efc-1ab2-484e-898c-caf40328f238

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution (m r s : ℕ) (h : r + s < m) :
    0 < matchingJacobianWeight m r s := by
  have hs : s ≤ m - 1 - r := by omega
  have hr : r ≤ m - 1 - s := by omega
  unfold matchingJacobianWeight
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.factorial_pos _)
      (Nat.descFactorial_pos.mpr hs))
    (Nat.descFactorial_pos.mpr hr)
end PermanentFormulaLowerBound
