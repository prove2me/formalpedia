-- Prove2me | solution 1 for PermanentRollout.homogeneousMapIdeal_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/2dae361f-de86-469a-b37a-44dab9b1a2c5

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
    {ι : Type*} (F : ι → MvPolynomial ι ℂ) (e : ℕ)
    (hF : ∀ i, (F i).IsHomogeneous e) :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ)
      (homogeneousMapIdeal F) := by
  classical
  unfold homogeneousMapIdeal
  apply Ideal.homogeneous_span
  rintro _ ⟨i, rfl⟩
  exact ⟨e, hF i⟩
end PermanentRollout
