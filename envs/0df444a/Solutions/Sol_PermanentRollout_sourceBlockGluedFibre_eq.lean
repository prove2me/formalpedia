-- Prove2me | solution 1 for PermanentRollout.sourceBlockGluedFibre_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/3b6b342c-b90c-4a87-9fb0-320f66969b21

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceBlockMatchingOf_sum_weight

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (I : Finset (Fin r)) (J : Finset (Fin s))
    (hJ : J.card = d) :
    sourceBlockGluedFibre r s d X U I J =
      ((s - d).factorial : R) *
        (sourceBlockAlpha r d U I * sourceBlockMinor r s X I J) := by
  exact sourceBlockMatchingOf_sum_weight r s d X U I J hJ
end PermanentRollout
