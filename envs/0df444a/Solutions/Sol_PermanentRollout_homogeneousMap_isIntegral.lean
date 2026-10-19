-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/ccc43d92-b932-4b03-b148-369c19bf5929

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    Algebra.IsIntegral (homogeneousMapSubalgebra F)
      (MvPolynomial ι ℂ) := by
  letI := homogeneousMap_moduleFinite F e he hF hzero
  exact Algebra.IsIntegral.of_finite _ _
end PermanentRollout
