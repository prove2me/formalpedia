-- Prove2me | solution 1 for WeierstrassCurve.diffAddNumP_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:17.55156+00:00
-- url     : https://prove2.me/submissions/62a8e039-092a-4e30-a0e9-444b9eb3c86f

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

/-- Eval bridge for `diffAddNumP`. -/
theorem _root_.solution (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (diffAddNumP W X0 Z0 X1 Z1).eval x =
      (sumNumP W X0 Z0 X1 Z1).eval x - ((deltaP W X0 Z0 X1 Z1).eval x) ^ 2 * x := by
  simp only [diffAddNumP, eval_sub, eval_mul, eval_pow, eval_X]

end

end WeierstrassCurve
