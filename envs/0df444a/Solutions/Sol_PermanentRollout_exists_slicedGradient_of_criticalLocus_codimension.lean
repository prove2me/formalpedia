-- Prove2me | solution 1 for PermanentRollout.exists_slicedGradient_of_criticalLocus_codimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/2a826544-29ac-420d-89ca-120d2fb53bf9

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_slicedGradient_of_projective_input_disjoint
import Theorems.Thm_PermanentRollout_exists_inputSlice_projective_disjoint_of_criticalLocus_codimension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m k c d : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d)
    (hk : k ≤ c) (hm : k < m)
    (hcodimension : criticalLocusDimension P ≤
      ((m - c : ℕ) : WithBot ℕ∞)) :
    ∃ (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
      (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ)),
      Function.Injective W ∧
      (∀ i : Fin k,
        (slicedGradientPolynomial P W A i).IsHomogeneous (d - 1)) ∧
      (∀ u : Fin k → ℂ,
        (∀ i : Fin k,
          MvPolynomial.eval u (slicedGradientPolynomial P W A i) = 0) ↔
            u = 0) := by
  obtain ⟨W, hW, hinput⟩ :=
    exists_inputSlice_projective_disjoint_of_criticalLocus_codimension
      P hd hP hk hm hcodimension
  obtain ⟨A, hdegree, hzero⟩ :=
    exists_slicedGradient_of_projective_input_disjoint
      P hd hP W hW hinput
  exact ⟨W, A, hW, hdegree, hzero⟩
end PermanentRollout
