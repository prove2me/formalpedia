-- Prove2me | solution 1 for PermanentRollout.linearCoordinatePolynomial_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/b6f6f3be-9a68-4afd-ba38-c1b9b7fb7a35

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
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ)) (row : Fin m) :
    (linearCoordinatePolynomial W row).IsHomogeneous 1 := by
  unfold linearCoordinatePolynomial
  exact MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
    (fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ j)
end PermanentRollout
