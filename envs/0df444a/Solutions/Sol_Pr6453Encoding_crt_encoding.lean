-- Prove2me | solution 1 for Pr6453Encoding.crt_encoding
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T22:37:56.387069+00:00
-- url     : https://prove2.me/submissions/feb033f3-9c7e-4ca2-8ff9-0a3cf6949884

/-
PR #6453: the CRT encoding of a product.
-/
import Mathlib

set_option autoImplicit false

namespace Pr6453Encoding

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **The encoding: evaluation at a point is multiplicative.** -/
theorem encode_mul (p q : R[X]) (x : R) : (p * q).eval x = p.eval x * q.eval x :=
  eval_mul (x := x)

/-- Evaluation is additive, so the encoding is linear. -/
theorem encode_add (p q : R[X]) (x : R) : (p + q).eval x = p.eval x + q.eval x :=
  eval_add (x := x)

/-- **The decoding is well defined**: on polynomials of degree below the number of points, the
encodings determine the polynomial. -/
theorem encode_injective {S : Finset R} {p q : R[X]}
    (hp : p.natDegree < S.card) (hq : q.natDegree < S.card)
    (h : ∀ x ∈ S, p.eval x = q.eval x) : p = q :=
  Polynomial.eq_of_natDegree_lt_card_of_eval_eq' p q S h (by omega)

/-- **The CRT encoding computes multiplication.** Evaluate two polynomials at the points of `S`,
multiply the values pointwise, and interpolate: what comes out is the product, provided the product
has degree below the number of points. -/
theorem crt_encoding {S : Finset R} (p q r : R[X])
    (hpq : (p * q).natDegree < S.card) (hr : r.natDegree < S.card)
    (h : ∀ x ∈ S, r.eval x = p.eval x * q.eval x) : r = p * q := by
  refine encode_injective hr hpq ?_
  intro x hx
  rw [h x hx, eval_mul (x := x)]

/-- The pointwise product of the encodings is bilinear: adding in either factor adds the encoded
product. -/
theorem crt_encoding_add_left (p p' q : R[X]) (x : R) :
    ((p + p') * q).eval x = (p * q).eval x + (p' * q).eval x := by
  rw [add_mul, eval_add (x := x)]

/-- Scaling in either factor scales the encoded product. -/
theorem crt_encoding_smul_left (c : R) (p q : R[X]) (x : R) :
    ((C c * p) * q).eval x = c * (p * q).eval x := by
  rw [eval_mul (x := x), eval_mul (x := x), eval_C, eval_mul (x := x)]
  ring

end Pr6453Encoding

/-- **The CRT encoding computes multiplication.** -/
theorem solution {R : Type*} [CommRing R] [IsDomain R] {S : Finset R} (p q r : Polynomial R)
    (hpq : (p * q).natDegree < S.card) (hr : r.natDegree < S.card)
    (h : ∀ x ∈ S, Polynomial.eval x r = Polynomial.eval x p * Polynomial.eval x q) :
    r = p * q :=
  Pr6453Encoding.crt_encoding p q r hpq hr h
