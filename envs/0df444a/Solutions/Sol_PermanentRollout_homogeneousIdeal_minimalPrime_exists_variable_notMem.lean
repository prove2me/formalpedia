-- Prove2me | solution 1 for PermanentRollout.homogeneousIdeal_minimalPrime_exists_variable_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/309aee0c-2070-4ef7-aae7-c54fe5c5bd93

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousIdeal_minimalPrime_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousPrime_le_idealOfVars
import Theorems.Thm_PermanentRollout_homogeneousIdeal_vertex_not_minimal_of_ringKrullDim_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {t : ℕ} (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (hpositive :
      (0 : WithBot ℕ∞) < ringKrullDim
        (MvPolynomial (Fin t) ℂ ⧸ I)) :
    ∀ P ∈ I.minimalPrimes,
      ∃ i : Fin t, MvPolynomial.X i ∉ P := by
  intro P hP
  by_contra hnone
  simp only [not_exists, not_not] at hnone
  have hvariables : MvPolynomial.idealOfVars (Fin t) ℂ ≤ P := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hnone i
  have hhomogeneous :=
    homogeneousIdeal_minimalPrime_isHomogeneous I P hI hP
  have hreverse : P ≤ MvPolynomial.idealOfVars (Fin t) ℂ :=
    homogeneousPrime_le_idealOfVars P hP.isPrime hhomogeneous
  have heq : P = MvPolynomial.idealOfVars (Fin t) ℂ :=
    le_antisymm hreverse hvariables
  exact homogeneousIdeal_vertex_not_minimal_of_ringKrullDim_pos
    I hI hpositive (heq ▸ hP)
end PermanentRollout
