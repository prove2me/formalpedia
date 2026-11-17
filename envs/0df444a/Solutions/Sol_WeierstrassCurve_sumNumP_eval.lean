-- Prove2me | solution 1 for WeierstrassCurve.sumNumP_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:26.193412+00:00
-- url     : https://prove2.me/submissions/ec7d7015-ea1e-4cff-9aa6-6960b6605152

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDiffAddCert
import Definitions.Def_WardSomos
import Definitions.Def_PsiInvariant

/-! Proofs of the lemmas stated in `Theorems.Thm_DivisionPolynomial_DifferentialAddition` and their helpers. -/

open Polynomial

open scoped Polynomial

open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Eval bridge for `sumNumP`. -/
theorem _root_.solution (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (sumNumP W X0 Z0 X1 Z1).eval x =
      2 * X0.eval x * X1.eval x * (X0.eval x * Z1.eval x + X1.eval x * Z0.eval x)
        + W.b₂ * X0.eval x * X1.eval x * Z0.eval x * Z1.eval x
        + W.b₄ * Z0.eval x * Z1.eval x * (X0.eval x * Z1.eval x + X1.eval x * Z0.eval x)
        + W.b₆ * (Z0.eval x) ^ 2 * (Z1.eval x) ^ 2 := by
  simp only [sumNumP, eval_add, eval_mul, eval_pow, eval_C]

end

end WeierstrassCurve
