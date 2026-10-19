-- Prove2me | solution 1 for PermanentRollout.exists_slicedGradient_of_projective_input_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/6a9e801a-f639-40cc-938c-3386aa8409e8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_gradientVector_after_embedding_ne_zero_of_projective_disjoint
import Theorems.Thm_PermanentRollout_slicedGradient_of_projective_disjoint
import Theorems.Thm_PermanentRollout_exists_outputSlice_projective_disjoint

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
    (hW : Function.Injective W)
    (hinput : Disjoint
      ((LinearMap.range W).projectivization : Set (ℙ ℂ (Fin m → ℂ)))
      (projectiveCriticalLocus P)) :
    ∃ A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ),
      (∀ i : Fin k,
        (slicedGradientPolynomial P W A i).IsHomogeneous (d - 1)) ∧
      (∀ u : Fin k → ℂ,
        (∀ i : Fin k,
          MvPolynomial.eval u (slicedGradientPolynomial P W A i) = 0) ↔
            u = 0) := by
  have hnonzero :=
    gradientVector_after_embedding_ne_zero_of_projective_disjoint
      P W hW hinput
  obtain ⟨A, houtput⟩ :=
    exists_outputSlice_projective_disjoint P hP W hnonzero
  exact ⟨A,
    slicedGradient_of_projective_disjoint P hd hP W A hW hinput houtput⟩
end PermanentRollout
