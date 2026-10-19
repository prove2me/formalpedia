-- Prove2me | solution 1 for PermanentRollout.linearCoordinatePolynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/2ceb7b78-60ba-42e4-8e81-2669effd68cf

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {k m : ℕ}
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (row : Fin m) (u : Fin k → ℂ) :
    MvPolynomial.eval u (linearCoordinatePolynomial W row) = W u row := by
  classical
  calc
    MvPolynomial.eval u (linearCoordinatePolynomial W row) =
        ∑ j : Fin k, (W (Pi.single j 1)) row * u j := by
      simp [linearCoordinatePolynomial]
    _ = W u row := by
      conv_rhs => rw [pi_eq_sum_univ' u]
      simp [Finset.sum_apply, mul_comm]
end PermanentRollout
