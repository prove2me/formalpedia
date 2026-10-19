-- Prove2me | solution 1 for PermanentRollout.multiplication_gate_equation_totalDegree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/b76b43ec-94d4-45df-bafe-63e14265f4c1

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} (j : ι) (left right : MvPolynomial ι ℂ)
    (hleft : left.totalDegree ≤ 1)
    (hright : right.totalDegree ≤ 1) :
    (MvPolynomial.X j - left * right).totalDegree ≤ 2 := by
  calc
    (MvPolynomial.X j - left * right).totalDegree ≤
        max (MvPolynomial.X j).totalDegree (left * right).totalDegree :=
      MvPolynomial.totalDegree_sub _ _
    _ ≤ max 1 (1 + 1) :=
      max_le_max (by simp)
        ((MvPolynomial.totalDegree_mul _ _).trans
          (Nat.add_le_add hleft hright))
    _ = 2 := by decide
end PermanentRollout
