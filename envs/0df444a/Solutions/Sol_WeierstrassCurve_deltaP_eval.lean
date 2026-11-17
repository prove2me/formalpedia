-- Prove2me | solution 1 for WeierstrassCurve.deltaP_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:16.775671+00:00
-- url     : https://prove2.me/submissions/f763f268-1c10-48e0-b082-0b82706a07d1

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

/-- Eval bridge for `deltaP`. -/
theorem _root_.solution (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (deltaP W X0 Z0 X1 Z1).eval x = X0.eval x * Z1.eval x - X1.eval x * Z0.eval x := by
  simp only [deltaP, eval_sub, eval_mul]

end

end WeierstrassCurve
