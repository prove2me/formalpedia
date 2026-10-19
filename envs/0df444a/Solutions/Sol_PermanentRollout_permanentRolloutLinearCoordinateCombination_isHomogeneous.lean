-- Prove2me | solution 1 for PermanentRollout.permanentRolloutLinearCoordinateCombination_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/468d3498-138a-459e-99d8-d94451555e40

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {t : ℕ} (c : Fin t → ℂ) :
    (permanentRolloutLinearCoordinateCombination t c).IsHomogeneous 1 := by
  change (∑ i, c i • MvPolynomial.X i) ∈
    MvPolynomial.homogeneousSubmodule (Fin t) ℂ 1
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (MvPolynomial.isHomogeneous_X ℂ i)
end PermanentRollout
