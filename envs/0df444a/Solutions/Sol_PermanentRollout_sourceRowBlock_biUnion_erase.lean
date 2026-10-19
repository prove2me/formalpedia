-- Prove2me | solution 1 for PermanentRollout.sourceRowBlock_biUnion_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/353bae03-05ba-4a74-bfe2-d92749f16629

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (b t : ℕ) (h : Fin b) :
    ((Finset.univ : Finset (Fin b)).erase h).biUnion
        (sourceRowBlock b t) =
      (Finset.univ : Finset (Fin (b * t))) \ sourceRowBlock b t h := by
  classical
  ext row
  simp [mem_sourceRowBlock]
end PermanentRollout
