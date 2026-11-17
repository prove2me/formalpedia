-- Prove2me | solution 1 for Polynomial.residuePower_cast
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:12.65333+00:00
-- url     : https://prove2.me/submissions/36641b6f-b33e-45d7-8e60-538006a120da

import Definitions.Def_Polynomial_BinomialResidue

set_option autoImplicit false

namespace Polynomial

/-- Modular exponentiation agrees with exponentiation in the residue ring. -/
theorem _root_.solution (value exponent modulus : ℕ) :
    (residuePower value exponent modulus : ZMod modulus) =
      (value : ZMod modulus) ^ exponent := by
  have hf (es : List ℕ) (z : ℕ) :
      ((es.foldl (fun w _ => w * value % modulus) z : ℕ) : ZMod modulus) =
        (z : ZMod modulus) * (value : ZMod modulus) ^ es.length := by
    induction es generalizing z with
    | nil => simp
    | cons e es ih =>
      rw [List.foldl_cons, ih]
      simp only [ZMod.natCast_mod, Nat.cast_mul, List.length_cons, pow_succ]
      ring
  simpa [residuePower] using hf (List.range exponent) 1

end Polynomial
