-- Prove2me | solution 1 for PermanentRollout.treeQuotientLinearForm_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/e4130c2d-1ae7-4c99-9fa0-bb2d639d9fe1

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r : ℕ}
    (block : Finset (Fin r)) :
    treeQuotientLinearForm (treeBlockVector block) =
      squareZeroBlockSum r block := by
  classical
  simp [treeQuotientLinearForm, treeBlockVector,
    squareZeroBlockSum]
end PermanentRollout
