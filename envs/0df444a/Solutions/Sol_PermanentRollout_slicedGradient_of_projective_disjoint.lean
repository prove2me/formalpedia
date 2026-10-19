-- Prove2me | solution 1 for PermanentRollout.slicedGradient_of_projective_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/38fd7511-e405-492f-bd7e-98f566e9423d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_slicedGradientPolynomial_isHomogeneous
import Theorems.Thm_PermanentRollout_slicedGradient_zero_fiber_of_kernel_avoidance
import Theorems.Thm_PermanentRollout_gradientVector_after_embedding_ne_zero_of_projective_disjoint
import Theorems.Thm_PermanentRollout_slicedGradient_kernel_avoidance_of_projective_disjoint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m k d : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hW : Function.Injective W)
    (hinput : Disjoint
      ((LinearMap.range W).projectivization : Set (ℙ ℂ (Fin m → ℂ)))
      (projectiveCriticalLocus P))
    (houtput : Disjoint
      (projectiveSlicedGradientImage P W)
      ((LinearMap.ker A).projectivization : Set (ℙ ℂ (Fin m → ℂ)))) :
    (∀ i : Fin k,
      (slicedGradientPolynomial P W A i).IsHomogeneous (d - 1)) ∧
    (∀ u : Fin k → ℂ,
      (∀ i : Fin k,
        MvPolynomial.eval u (slicedGradientPolynomial P W A i) = 0) ↔
          u = 0) := by
  refine ⟨fun i => slicedGradientPolynomial_isHomogeneous P hP W A i, ?_⟩
  apply slicedGradient_zero_fiber_of_kernel_avoidance P hd hP W A
  exact slicedGradient_kernel_avoidance_of_projective_disjoint P W A
    (gradientVector_after_embedding_ne_zero_of_projective_disjoint
      P W hW hinput)
    houtput
end PermanentRollout
