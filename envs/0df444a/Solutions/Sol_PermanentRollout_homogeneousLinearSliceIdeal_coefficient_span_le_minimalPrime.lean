-- Prove2me | solution 1 for PermanentRollout.homogeneousLinearSliceIdeal_coefficient_span_le_minimalPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/cb07fa45-9776-4685-9d19-b0a8369fc8a4

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
    {t n : ℕ} (I : Ideal (MvPolynomial (Fin t) ℂ))
    (c : Fin n → Fin t → ℂ)
    (P : Ideal (MvPolynomial (Fin t) ℂ))
    (hP : P ∈ (homogeneousLinearSliceIdeal I c).minimalPrimes) :
    Submodule.span ℂ (Set.range c) ≤
      (P.restrictScalars ℂ).comap
        (permanentRolloutLinearCoordinateCombination t) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change permanentRolloutLinearCoordinateCombination t (c j) ∈ P
  apply hP.le
  exact (show Ideal.span (Set.range fun k =>
    permanentRolloutLinearCoordinateCombination t (c k)) ≤
      homogeneousLinearSliceIdeal I c from le_sup_right)
    (Ideal.subset_span ⟨j, rfl⟩)
end PermanentRollout
