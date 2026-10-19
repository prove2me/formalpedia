-- Prove2me | solution 1 for PermanentRollout.homogeneousIdeal_vertex_not_minimal_of_ringKrullDim_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/dbf418e1-cf54-46f0-8b7e-5f05600c6630

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_submoduleVanishingIdealCoordinateRing_ringKrullDim
import Theorems.Thm_PermanentRollout_homogeneousIdeal_radical_eq_idealOfVars_of_vertex_minimal

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (hpositive :
      (0 : WithBot ℕ∞) < ringKrullDim
        (MvPolynomial (Fin t) ℂ ⧸ I)) :
    MvPolynomial.idealOfVars (Fin t) ℂ ∉ I.minimalPrimes := by
  intro hvertex
  have hradical :=
    homogeneousIdeal_radical_eq_idealOfVars_of_vertex_minimal
      I hI hvertex
  have hvertexDimension :
      ringKrullDim
        (MvPolynomial (Fin t) ℂ ⧸
          MvPolynomial.idealOfVars (Fin t) ℂ) =
        (0 : WithBot ℕ∞) := by
    rw [← vanishingIdeal_origin_eq_idealOfVars]
    simpa using
      submoduleVanishingIdealCoordinateRing_ringKrullDim
        (⊥ : Submodule ℂ (Fin t → ℂ))
  have hzero :
      ringKrullDim (MvPolynomial (Fin t) ℂ ⧸ I) =
        (0 : WithBot ℕ∞) := by
    calc
      ringKrullDim (MvPolynomial (Fin t) ℂ ⧸ I) =
          ringKrullDim (MvPolynomial (Fin t) ℂ ⧸ I.radical) := by
        rw [ringKrullDim_quotient, ringKrullDim_quotient,
          PrimeSpectrum.zeroLocus_radical]
      _ = ringKrullDim
          (MvPolynomial (Fin t) ℂ ⧸
            MvPolynomial.idealOfVars (Fin t) ℂ) := by rw [hradical]
      _ = (0 : WithBot ℕ∞) := hvertexDimension
  rw [hzero] at hpositive
  exact (lt_irrefl _ hpositive)
end PermanentRollout
