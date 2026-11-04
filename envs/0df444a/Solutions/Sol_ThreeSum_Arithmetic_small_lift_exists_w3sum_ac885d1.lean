-- Prove2me | solution 1 for ThreeSum.Arithmetic.small_lift_exists_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:58.136973+00:00
-- url     : https://prove2.me/submissions/4dbc8a1a-3a1a-4a02-aac0-182a3fb170db

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution {P a b c : ℤ} (hP : 0 < P)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hdiv : P ∣ c - b - a) :
    ∃ j : ℤ, SmallLift j ∧ c - b = a + j * P := by
  obtain ⟨j, hj⟩ := hdiv
  have hjlo : -1 ≤ j := by
    by_contra h
    have hj' : j ≤ -2 := by omega
    have hm := mul_le_mul_of_nonneg_left hj' hP.le
    nlinarith
  have hjhi : j ≤ 0 := by
    by_contra h
    have hj' : 1 ≤ j := by omega
    have hm := mul_le_mul_of_nonneg_left hj' hP.le
    nlinarith
  refine ⟨j, ?_, ?_⟩
  · unfold SmallLift
    omega
  · nlinarith
end ThreeSum.Arithmetic
