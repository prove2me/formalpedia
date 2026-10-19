-- Prove2me | solution 1 for PermanentRollout.slicedGradientPolynomial_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/ac6f437e-c0e7-4609-bd55-cde9bbcc4f6c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneous_eval_zero_of_pos
import Theorems.Thm_PermanentRollout_slicedGradientPolynomial_isHomogeneous

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
    (i : Fin k) :
    MvPolynomial.eval (0 : Fin k → ℂ)
        (slicedGradientPolynomial P W A i) = 0 := by
  exact homogeneous_eval_zero_of_pos (by omega)
    (slicedGradientPolynomial_isHomogeneous P hP W A i)
end PermanentRollout
