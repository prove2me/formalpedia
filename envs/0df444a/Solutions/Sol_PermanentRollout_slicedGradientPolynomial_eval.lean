-- Prove2me | solution 1 for PermanentRollout.slicedGradientPolynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/a746f192-09eb-4273-962b-ad1dc35b8bb3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_eval_aeval_linearCoordinatePolynomial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (i : Fin k) (u : Fin k → ℂ) :
    MvPolynomial.eval u (slicedGradientPolynomial P W A i) =
      A (gradientVector P (W u)) i := by
  classical
  calc
    MvPolynomial.eval u (slicedGradientPolynomial P W A i) =
        ∑ j : Fin m,
          (A (Pi.single j 1)) i *
            MvPolynomial.eval (W u) (MvPolynomial.pderiv j P) := by
      simp only [slicedGradientPolynomial, map_sum,
        MvPolynomial.eval_mul, MvPolynomial.eval_C]
      apply Finset.sum_congr rfl
      intro j _
      rw [eval_aeval_linearCoordinatePolynomial]
    _ = A (gradientVector P (W u)) i := by
      conv_rhs => rw [pi_eq_sum_univ' (gradientVector P (W u))]
      simp [gradientVector, Finset.sum_apply, mul_comm]
end PermanentRollout
