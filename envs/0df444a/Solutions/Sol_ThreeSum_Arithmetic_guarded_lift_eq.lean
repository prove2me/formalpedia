-- Prove2me | solution 1 for ThreeSum.Arithmetic.guarded_lift_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:17:02.755454+00:00
-- url     : https://prove2.me/submissions/78ed8124-cdf8-4c6f-95d6-898d30480c09

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Theorems.Thm_ThreeSum_Arithmetic_eq_zero_of_dvd_of_bounds

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
    (hcong : R ∣ (c + d - b) - (a + j * P + d)) :
    c - b = a + j * P := by
  have hR : 0 < R := by omega
  have hdiv : R ∣ c - b - a - j * P := by
    convert hcong using 1 <;> ring
  have hbds : -R < c - b - a - j * P ∧ c - b - a - j * P < R := by
    rcases hj with rfl | rfl | rfl <;> constructor <;> nlinarith
  have hz := eq_zero_of_dvd_of_bounds hR hbds.1 hbds.2 hdiv
  linarith
end ThreeSum.Arithmetic
