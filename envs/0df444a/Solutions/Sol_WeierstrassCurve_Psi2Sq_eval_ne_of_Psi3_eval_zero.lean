-- Prove2me | solution 1 for WeierstrassCurve.Psi2Sq_eval_ne_of_Psi3_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:15.93872+00:00
-- url     : https://prove2.me/submissions/08713fd0-c744-47d6-9805-23ada1b0123d

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneResultantCerts
import Definitions.Def_WardSomos
import Theorems.Thm_WeierstrassCurve_Psi3_eval_ne_of_Psi2Sq_eval_zero

/-! Proofs of the lemmas stated in `Theorems.Thm_DivisionPolynomial_ResultantNonsingularity` and their helpers. -/

open Polynomial

open scoped Polynomial

open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

theorem _root_.solution (W : WeierstrassCurve k) [W.IsElliptic] {x : k}
    (hc3 : W.Ψ₃.eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 :=
  fun hs => Psi3_eval_ne_of_Psi2Sq_eval_zero W hs hc3

end

end WeierstrassCurve
