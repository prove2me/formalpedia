-- Prove2me | solution 1 for PermanentRollout.treeQuotientLinearForm_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/b909845d-9a9b-4078-8e09-93e07f28e132

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r : ℕ}
    (a : ℂ) (vector : Fin r → ℂ) :
    treeQuotientLinearForm (fun row => a * vector row) =
      algebraMap ℂ (SquareZeroAlgebra r) a *
        treeQuotientLinearForm vector := by
  simp [treeQuotientLinearForm, Finset.mul_sum, mul_assoc]
end PermanentRollout
