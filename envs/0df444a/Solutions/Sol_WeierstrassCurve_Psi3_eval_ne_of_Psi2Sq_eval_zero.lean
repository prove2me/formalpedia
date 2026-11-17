-- Prove2me | solution 1 for WeierstrassCurve.Psi3_eval_ne_of_Psi2Sq_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:15.072623+00:00
-- url     : https://prove2.me/submissions/a0b39f22-e7cb-4ff8-8323-42055ae8993b

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneResultantCerts
import Definitions.Def_WardSomos

/-! Proofs of the lemmas stated in `Theorems.Thm_DivisionPolynomial_ResultantNonsingularity` and their helpers. -/

open Polynomial

open scoped Polynomial

open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

/-- `b_relation` in distributed-C form. -/
private lemma bRelC (W : WeierstrassCurve k) :
    C W.b₂ * C W.b₆ - (C W.b₄) ^ 2 - C 4 * C W.b₈ = (0 : k[X]) := by
  have h0 : W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0 := by
    have hb := W.b_relation; linear_combination -hb
  have := congrArg (fun z : k => (C z : k[X])) h0
  simpa [map_sub, map_mul, map_pow] using this

/-- Resultant/Bezout certificate `A·Ψ₂Sq + B·Ψ₃ = C(-Δ²)` (CAS-extracted, uses `b_relation`). -/
private lemma bezout_Ψ₂Sq_Ψ₃ (W : WeierstrassCurve k) :
    (-(6 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆)
          + (6 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          - (12 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₈)
          + (252 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (216 : k[X]) * X ^ 3 * (C W.b₄) ^ 3
          + (288 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₈)
          - (972 : k[X]) * X ^ 3 * (C W.b₆) ^ 2
          - (2 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆)
          + (2 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - X ^ 2 * (C W.b₂) ^ 3 * (C W.b₈)
          + (81 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          - (72 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3
          - (351 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 2
          + (108 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          + (432 : k[X]) * X ^ 2 * (C W.b₆) * (C W.b₈)
          + X * (C W.b₂) ^ 4 * (C W.b₈)
          - (7 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          + (6 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          - (50 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          - (3 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          + (288 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (168 : k[X]) * X * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (216 : k[X]) * X * (C W.b₄) ^ 4
          + (432 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₈)
          - (1134 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 2
          - (192 : k[X]) * X * (C W.b₈) ^ 2
          + (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈)
          - (4 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 2
          + (3 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          - (7 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈)
          - (36 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈)
          + (162 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2
          - (16 : k[X]) * (C W.b₂) * (C W.b₈) ^ 2
          - (108 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆)
          + (432 : k[X]) * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - (729 : k[X]) * (C W.b₆) ^ 3) * W.Ψ₂Sq
      + ((8 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆)
          - (8 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          + (16 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₈)
          - (336 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (288 : k[X]) * X ^ 2 * (C W.b₄) ^ 3
          - (384 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₈)
          + (1296 : k[X]) * X ^ 2 * (C W.b₆) ^ 2
          + (2 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆)
          - (2 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (80 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          + (72 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3
          + (32 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₈)
          + (360 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 2
          - (144 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆)
          - (576 : k[X]) * X * (C W.b₆) * (C W.b₈)
          - (C W.b₂) ^ 4 * (C W.b₈)
          + (5 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          - (4 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          + (48 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          + (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          - (204 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          - (176 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈)
          + (144 : k[X]) * (C W.b₄) ^ 4
          - (384 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈)
          + (864 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2
          + (256 : k[X]) * (C W.b₈) ^ 2) * W.Ψ₃
      = C (- W.Δ ^ 2) := by
  have hb := bRelC W
  linear_combination (norm :=
    (simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.Δ,
      map_neg, map_mul, map_add, map_sub, map_pow, map_ofNat, map_one,
      Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_1]; ring1))
    ((-(12 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          - (4 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          + (80 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (32 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (64 : k[X]) * (C W.b₄) ^ 4
          + (112 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈)
          - (324 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2
          - (64 : k[X]) * (C W.b₈) ^ 2)) * hb

/-- On an elliptic curve, `Ψ₂Sq` and `Ψ₃` have no common root. -/
theorem _root_.solution (W : WeierstrassCurve k) [W.IsElliptic] {x : k}
    (hs : W.Ψ₂Sq.eval x = 0) : W.Ψ₃.eval x ≠ 0 := by
  intro hc3
  have hb := congrArg (fun p : k[X] => p.eval x) (bezout_Ψ₂Sq_Ψ₃ W)
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_neg, eval_ofNat, eval_X,
    hs, hc3, mul_zero, zero_mul, add_zero] at hb
  have hΔ2 : W.Δ ^ 2 = 0 := by linear_combination hb
  exact (W.isUnit_Δ.ne_zero) (pow_eq_zero_iff (by norm_num) |>.mp hΔ2)

end

end WeierstrassCurve
