-- Prove2me | solution 1 for ThreeSum.Arithmetic.guarded_lift_eq_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:06.962387+00:00
-- url     : https://prove2.me/submissions/5143d4d3-b477-40b7-8df2-c38f50b347bf

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Theorems.Thm_ThreeSum_Arithmetic_guarded_lift_eq

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : SmallLift j)
    (hkey : Int.ModEq R (a + j * P + d) (c + d - b)) :
    c - b = a + j * P :=
  guarded_lift_eq hP hguard ha0 haP hb0 hbP hc0 hcP hj hkey.dvd
end ThreeSum.Arithmetic
