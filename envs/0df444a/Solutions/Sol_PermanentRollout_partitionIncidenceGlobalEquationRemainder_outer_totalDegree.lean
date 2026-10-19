-- Prove2me | solution 1 for PermanentRollout.partitionIncidenceGlobalEquationRemainder_outer_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/3c382616-9f67-4634-97bd-7ca76b111ecd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partitionIncidenceGlobalEquationRemainder_outer_totalDegree_aux

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (t s d : ℕ) (a : Fin s) (i : Fin t) :
    (partitionIncidenceGlobalColumnLift t s d
      (partitionIncidenceGlobalEquationRemainder t s d a i)).totalDegree ≤
      d - 2 :=
  partitionIncidenceGlobalEquationRemainder_outer_totalDegree_aux t s d a i
end PermanentRollout
