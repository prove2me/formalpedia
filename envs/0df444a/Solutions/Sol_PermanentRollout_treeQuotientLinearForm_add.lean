-- Prove2me | solution 1 for PermanentRollout.treeQuotientLinearForm_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/bc1b7e28-90ae-46bb-bb36-e48d8169c2f5

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r : ℕ}
    (left right : Fin r → ℂ) :
    treeQuotientLinearForm (fun row => left row + right row) =
      treeQuotientLinearForm left + treeQuotientLinearForm right := by
  simp [treeQuotientLinearForm, add_mul, Finset.sum_add_distrib]
end PermanentRollout
