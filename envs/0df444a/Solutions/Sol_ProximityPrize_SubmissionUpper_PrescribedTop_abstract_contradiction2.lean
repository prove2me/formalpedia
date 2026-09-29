-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.PrescribedTop.abstract_contradiction2
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T18:03:30.35336+00:00
-- url     : https://prove2.me/submissions/67eee537-0552-413f-89d3-7c5556ded2cd

import Mathlib
import Init
/-!
# A prescribed-top-coefficient collision family below half radius

The included baseline attacks at radius `1/2` using the word `X^m` together with
*every* `m`-subset of the domain as an interpolation set.  This file generalises
that construction: it uses `t`-subsets with `t = m + r`, restricted to those whose
vanishing polynomial shares its top `r` coefficients with a fixed one.  Each such
subset still yields a genuine codeword agreeing with a single fixed word on all `t`
points, so the attack survives at radius `(n - t)/n = 1/2 - r/n`.

With `r = 8431` this certifies the unsafe suffix from grid index `122641` onward.
-/

namespace ProximityPrize.SubmissionUpper.PrescribedTop

open Polynomial
                                   
                             
open scoped NNReal


                             






























































theorem _root_.solution {Ca Cb U L P W V F four c : ℕ}
    (hF : 0 < F) (hV : 0 < V)
    (hshift : Cb * U = Ca * L)
    (hup : F * U ^ 2 ≤ W)
    (hlo : V ≤ L ^ 2)
    (hcb : four < c * Ca)
    (hcon : Cb ≤ P)
    (hnum : c ^ 2 * P ^ 2 * W ≤ F * four ^ 2 * V) : False := (by
  have hFV : 0 < F * V := Nat.mul_pos hF hV
  have hsq : four ^ 2 < (c * Ca) ^ 2 := Nat.pow_lt_pow_left hcb (by norm_num)
  have hstep : F * four ^ 2 * V < F * (c * Ca) ^ 2 * V := by
    calc F * four ^ 2 * V = four ^ 2 * (F * V) := by ring
      _ < (c * Ca) ^ 2 * (F * V) := Nat.mul_lt_mul_of_lt_of_le hsq (le_refl (F * V)) hFV
      _ = F * (c * Ca) ^ 2 * V := by ring
  have hstrict : F * four ^ 2 * V < c ^ 2 * P ^ 2 * W := by
    calc F * four ^ 2 * V
        < F * (c * Ca) ^ 2 * V := hstep
      _ ≤ F * (c * Ca) ^ 2 * L ^ 2 := Nat.mul_le_mul_left _ hlo
      _ = c ^ 2 * (F * (Ca * L) ^ 2) := by ring
      _ = c ^ 2 * (F * (Cb * U) ^ 2) := by rw [hshift]
      _ = c ^ 2 * Cb ^ 2 * (F * U ^ 2) := by ring
      _ ≤ c ^ 2 * Cb ^ 2 * W := Nat.mul_le_mul_left _ hup
      _ ≤ c ^ 2 * P ^ 2 * W :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcon 2))
  exact absurd hnum (not_le.mpr hstrict)
)
end PrescribedTop
end SubmissionUpper
end ProximityPrize
