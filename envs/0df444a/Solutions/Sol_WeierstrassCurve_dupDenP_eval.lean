-- Prove2me | solution 1 for WeierstrassCurve.dupDenP_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:18.256249+00:00
-- url     : https://prove2.me/submissions/0e182765-cfee-4513-8189-c1ebbdc16c60

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDoubling

/-! Proofs of the lemmas stated in `Theorems.Thm_DivisionPolynomial_Duplication` and their helpers. -/

namespace WeierstrassCurve

open Polynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Eval bridge: `dupDenP` evaluated is the value-level doubling denominator. -/
theorem _root_.solution (W : WeierstrassCurve R) (Xc Zc : R[X]) (x : R) :
    (W.dupDenP Xc Zc).eval x
      = 4 * (Xc.eval x) ^ 3 * (Zc.eval x) + W.b₂ * (Xc.eval x) ^ 2 * (Zc.eval x) ^ 2
        + 2 * W.b₄ * (Xc.eval x) * (Zc.eval x) ^ 3 + W.b₆ * (Zc.eval x) ^ 4 := by
  simp only [dupDenP, eval_add, eval_mul, eval_pow, eval_C, eval_ofNat]

end WeierstrassCurve
