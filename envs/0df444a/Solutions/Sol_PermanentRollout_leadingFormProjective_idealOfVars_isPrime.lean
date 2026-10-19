-- Prove2me | solution 1 for PermanentRollout.leadingFormProjective_idealOfVars_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/603de8ea-4b21-4e0b-b616-28bdea038df2

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution (t : ℕ) :
    (MvPolynomial.idealOfVars (Fin t) ℂ).IsPrime := by
  rw [← vanishingIdeal_origin_eq_idealOfVars]
  infer_instance
end PermanentRollout
