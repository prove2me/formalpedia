-- Prove2me | solution 1 for PermanentRollout.eval_aeval_linearCoordinatePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/e51b2ae3-375d-4c93-8ccb-ece2cc4a07ea

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_linearCoordinatePolynomial_eval

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {k m : ℕ}
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (u : Fin k → ℂ) (f : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.eval u
        (MvPolynomial.aeval (fun row => linearCoordinatePolynomial W row) f) =
      MvPolynomial.eval (W u) f := by
  change
    (MvPolynomial.aeval u)
        (MvPolynomial.aeval (fun row => linearCoordinatePolynomial W row) f) =
      (MvPolynomial.aeval (W u)) f
  have hcoordinates :
      (fun row =>
        (MvPolynomial.aeval u) (linearCoordinatePolynomial W row)) =
        W u := by
    funext row
    exact linearCoordinatePolynomial_eval W row u
  rw [MvPolynomial.comp_aeval_apply, hcoordinates]
end PermanentRollout
