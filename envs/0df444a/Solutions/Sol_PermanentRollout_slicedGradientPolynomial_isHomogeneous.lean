-- Prove2me | solution 1 for PermanentRollout.slicedGradientPolynomial_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/66221328-e905-4727-9b11-f9f0985cb0e2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_linearCoordinatePolynomial_isHomogeneous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m k d : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (hP : P.IsHomogeneous d)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (i : Fin k) :
    (slicedGradientPolynomial P W A i).IsHomogeneous (d - 1) := by
  unfold slicedGradientPolynomial
  refine MvPolynomial.IsHomogeneous.sum Finset.univ _ (d - 1) ?_
  intro j _
  simpa only [one_mul] using
    ((hP.pderiv (i := j)).aeval
      (fun row => linearCoordinatePolynomial W row)
      (fun row => linearCoordinatePolynomial_isHomogeneous W row)).C_mul
        ((A (Pi.single j 1)) i)
end PermanentRollout
