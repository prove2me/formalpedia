-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_homogeneous_linear_slice_coefficient_span_le_minimalPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/db8a8544-2346-4e71-971b-6844382e5014

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
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (c : Fin n → Fin m → ℂ)
    (p : Ideal (MvPolynomial (Fin m) ℂ))
    (hp : p ∈ (permanentRolloutHomogeneousLinearSliceIdeal I c).minimalPrimes) :
    Submodule.span ℂ (Set.range c) ≤
      (p.restrictScalars ℂ).comap
        (permanentRolloutLinearCoordinateCombination m) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change permanentRolloutLinearCoordinateCombination m (c j) ∈ p
  apply hp.le
  exact (show Ideal.span (Set.range fun j =>
      permanentRolloutLinearCoordinateCombination m (c j)) ≤
        permanentRolloutHomogeneousLinearSliceIdeal I c from
      le_sup_right) (Ideal.subset_span ⟨j, rfl⟩)
end PermanentRollout
