-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_linearCoordinateCombination_isHomogeneousElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/e6ff28e0-db8e-484b-8377-b6f92db4c9c3

import Mathlib
import Definitions.Def_Permanent

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
    {m : ℕ} (c : Fin m → ℂ) :
    SetLike.IsHomogeneousElem
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ)
      (permanentRolloutLinearCoordinateCombination m c) := by
  refine ⟨1, ?_⟩
  change (∑ i, c i • MvPolynomial.X i) ∈
    MvPolynomial.homogeneousSubmodule (Fin m) ℂ 1
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (MvPolynomial.isHomogeneous_X ℂ i)
end PermanentRollout
