-- Prove2me | solution 1 for Polynomial.binomialBlocksResidue_cast
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:11.256253+00:00
-- url     : https://prove2.me/submissions/421fa3be-3600-4f47-bbe5-121ca35e28b8

import Definitions.Def_Polynomial_BinomialResidue

set_option autoImplicit false

namespace Polynomial

private theorem factor_cast (base count value exponent : ℕ) (hb : 0 < base) :
    (binomialResidue base count value exponent : ZMod (base ^ count)) =
      (value : ZMod (base ^ count)) * (1 - (base : ZMod (base ^ count)) ^ exponent) := by
  have hm : 0 < base ^ count := pow_pos hb _
  by_cases he : exponent < count
  · rw [binomialResidue, if_pos he]
    dsimp only
    split_ifs with hs
    · rw [Nat.cast_sub hs]
      simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow]
      ring
    · have ht : (value * base ^ exponent) % base ^ count < base ^ count :=
        Nat.mod_lt _ hm
      rw [Nat.cast_sub (by omega :
        (value * base ^ exponent) % base ^ count ≤ value + base ^ count)]
      simp only [Nat.cast_add, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow]
      have hz : (base : ZMod (base ^ count)) ^ count = 0 := by
        exact_mod_cast (ZMod.natCast_self (base ^ count))
      rw [hz]
      ring
  · rw [binomialResidue, if_neg he]
    have hz : (base : ZMod (base ^ count)) ^ count = 0 := by
      exact_mod_cast (ZMod.natCast_self (base ^ count))
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt he)
    rw [hd, pow_add, hz, zero_mul, sub_zero, mul_one]

/-- The modular evaluator represents the evaluation of the actual integer polynomial. -/
theorem _root_.solution (base count : ℕ) (hb : 0 < base)
    (blocks : List (List ℕ)) :
    (binomialBlocksResidue base count blocks : ZMod (base ^ count)) =
      (binomialBlocksPolynomial blocks).eval₂ (Int.castRingHom (ZMod (base ^ count)))
        (base : ZMod (base ^ count)) := by
  let R := ZMod (base ^ count)
  let φ : ℤ[X] →+* R := eval₂RingHom (Int.castRingHom R) (base : R)
  have inner (es : List ℕ) (value : ℕ) :
      ((es.foldl (binomialResidue base count) value : ℕ) : R) =
        (value : R) * φ ((es.map fun e => (1 - X ^ e : ℤ[X])).prod) := by
    induction es generalizing value with
    | nil => simp
    | cons e es ih =>
      rw [List.foldl_cons, ih, factor_cast base count value e hb]
      simp only [List.map_cons, List.prod_cons, map_mul, map_sub, map_one, map_pow]
      have hX : φ X = (base : R) := Polynomial.eval₂_X _ _
      rw [hX]
      change ((value : R) * (1 - (base : R)^e)) * _ =
        (value : R) * ((1 - (base : R)^e) * _)
      ring
  have outer (bs : List (List ℕ)) (value : ℕ) :
      ((bs.foldl (fun v es => es.foldl (binomialResidue base count) v) value : ℕ) : R) =
        (value : R) * φ (binomialBlocksPolynomial bs) := by
    induction bs generalizing value with
    | nil => simp [binomialBlocksPolynomial]
    | cons es bs ih =>
      rw [List.foldl_cons, ih, inner]
      simp only [binomialBlocksPolynomial, List.map_cons, List.prod_cons, map_mul]
      ring
  simpa only [binomialBlocksResidue, Nat.cast_one, one_mul, R, φ, Polynomial.coe_eval₂RingHom] using outer blocks 1

end Polynomial
