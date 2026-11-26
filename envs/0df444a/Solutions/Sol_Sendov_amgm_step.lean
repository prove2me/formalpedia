-- Prove2me | solution 1 for Sendov.amgm_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:22.764188+00:00
-- url     : https://prove2.me/submissions/3c2fd9fa-c471-4d82-b560-c022ca7524f5

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Maclaurin

set_option autoImplicit false
open Sendov
open Multiset
variable {a : ℝ} {t : Multiset ℝ}
namespace Sendov
theorem _root_.solution (N : ℕ) {u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    a * u ^ N ≤ ((a + N * u) / (N + 1)) ^ (N + 1) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set w : ℝ := (a + N * u) / ((N + 1) * u) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hbase : (a + (N : ℝ) * u) / ((N : ℝ) + 1) = w * u := by
    rw [hw]; field_simp
  have hber : 1 + ((N : ℝ) + 1) * (w - 1) ≤ w ^ (N + 1) := by
    have := one_add_mul_le_pow (a := w - 1) (by linarith) (N + 1)
    simpa using this
  have hau : a / u = ((N : ℝ) + 1) * w - N := by
    rw [hw]; field_simp; ring
  have hkey : a / u ≤ w ^ (N + 1) := by linarith [hber]
  rw [hbase, mul_pow]
  have : a ≤ w ^ (N + 1) * u := by
    rw [div_le_iff₀ hu] at hkey; linarith
  calc a * u ^ N ≤ (w ^ (N + 1) * u) * u ^ N := by
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = w ^ (N + 1) * u ^ (N + 1) := by ring
end Sendov
