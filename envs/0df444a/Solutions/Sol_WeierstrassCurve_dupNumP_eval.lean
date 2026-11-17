-- Prove2me | solution 1 for WeierstrassCurve.dupNumP_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:19.170808+00:00
-- url     : https://prove2.me/submissions/8b067e19-45e1-4888-b9cb-f715fd74386a

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDoubling

/-! Proofs of the lemmas stated in `Theorems.Thm_DivisionPolynomial_Duplication` and their helpers. -/

namespace WeierstrassCurve

open Polynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Eval bridge: `dupNumP` evaluated is the value-level doubling numerator (in `W.b_i`). -/
theorem _root_.solution (W : WeierstrassCurve R) (Xc Zc : R[X]) (x : R) :
    (W.dupNumP Xc Zc).eval x
      = (Xc.eval x) ^ 4 - W.b₄ * (Xc.eval x) ^ 2 * (Zc.eval x) ^ 2
        - 2 * W.b₆ * (Xc.eval x) * (Zc.eval x) ^ 3 - W.b₈ * (Zc.eval x) ^ 4 := by
  simp only [dupNumP, eval_sub, eval_mul, eval_pow, eval_C]

end WeierstrassCurve
