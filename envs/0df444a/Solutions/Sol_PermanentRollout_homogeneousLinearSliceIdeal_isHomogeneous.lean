-- Prove2me | solution 1 for PermanentRollout.homogeneousLinearSliceIdeal_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/5041139e-5684-40f0-8454-ec6ee0182a77

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanentRolloutLinearCoordinateCombination_isHomogeneous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution {t n : ℕ}
    (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (c : Fin n → Fin t → ℂ) :
    (homogeneousLinearSliceIdeal I c).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ) := by
  unfold homogeneousLinearSliceIdeal
  apply hI.sup
  apply Ideal.homogeneous_span
  rintro _ ⟨j, rfl⟩
  exact ⟨1, permanentRolloutLinearCoordinateCombination_isHomogeneous (c j)⟩
end PermanentRollout
