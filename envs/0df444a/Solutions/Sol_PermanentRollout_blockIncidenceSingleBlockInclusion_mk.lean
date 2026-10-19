-- Prove2me | solution 1 for PermanentRollout.blockIncidenceSingleBlockInclusion_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/cd04878d-b2eb-42ca-b76a-02a0612ed269

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (block : Fin b)
    (p : MvPolynomial (IncidenceCoordinate t s) ℂ) :
    blockIncidenceSingleBlockInclusion b t s d block
      (Ideal.Quotient.mk (partitionIncidenceIdeal t s d) p) =
      Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
        (MvPolynomial.rename
          (fun z : IncidenceCoordinate t s => (block, z)) p) := by
  rfl
end PermanentRollout
