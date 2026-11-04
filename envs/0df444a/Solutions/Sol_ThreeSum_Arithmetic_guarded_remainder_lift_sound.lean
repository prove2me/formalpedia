-- Prove2me | solution 1 for ThreeSum.Arithmetic.guarded_remainder_lift_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:19.691572+00:00
-- url     : https://prove2.me/submissions/487417ff-9379-41f4-9ee8-e98de364a963

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Theorems.Thm_ThreeSum_Arithmetic_arithmetic_dvd_of_guarded_lift

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R) (hj : SmallLift j)
    (hkey : Int.ModEq R (a % P + j * P + d) (c % P + d - b % P)) :
    P ∣ c - b - a := by
  have hp0 : P ≠ 0 := ne_of_gt hP
  have hnorm : P ∣ c % P - b % P - a % P :=
    arithmetic_dvd_of_guarded_lift hP hguard
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP)
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP)
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP) hj hkey.dvd
  have heq : Int.ModEq P (c % P - b % P - a % P) (c - b - a) :=
    ((Int.mod_modEq c P).sub (Int.mod_modEq b P)).sub (Int.mod_modEq a P)
  exact Int.modEq_zero_iff_dvd.mp (heq.symm.trans hnorm.modEq_zero_int)
end ThreeSum.Arithmetic
