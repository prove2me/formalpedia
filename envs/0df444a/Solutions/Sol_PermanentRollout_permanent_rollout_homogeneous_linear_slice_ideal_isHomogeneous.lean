-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_homogeneous_linear_slice_ideal_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/76e6b968-01e1-43f0-b2d4-3d3adeacaddc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_linearCoordinateCombination_isHomogeneousElem

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ))
    (c : Fin n → Fin m → ℂ) :
    (permanentRolloutHomogeneousLinearSliceIdeal I c).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ) := by
  unfold permanentRolloutHomogeneousLinearSliceIdeal
  apply hI.sup
  apply Ideal.homogeneous_span
  rintro _ ⟨j, rfl⟩
  exact permanent_rollout_linearCoordinateCombination_isHomogeneousElem (c j)
end PermanentRollout
