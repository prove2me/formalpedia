-- Prove2me | solution 1 for Sendov.maclaurin_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:37.425593+00:00
-- url     : https://prove2.me/submissions/394bc89f-8ade-4db7-9c12-4c239a0cc7dd

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
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    u ^ N + N * a * u ^ (N - 1) ≤ ((N : ℝ) + 1) * ((a + N * u) / (N + 1)) ^ N := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set w : ℝ := (a + N * u) / ((N + 1) * u) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hbase : (a + (N : ℝ) * u) / ((N : ℝ) + 1) = w * u := by
    rw [hw]; field_simp
  have hber : 1 + (N : ℝ) * (w - 1) ≤ w ^ N := by
    have := one_add_mul_le_pow (a := w - 1) (by linarith) N
    simpa using this
  have hau : a / u = ((N : ℝ) + 1) * w - N := by
    rw [hw]; field_simp; ring
  -- `u ^ N = u ^ (N-1) * u`
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hpow : u ^ (m + 1) = u ^ m * u := by ring
  rw [hbase, mul_pow]
  simp only [Nat.add_sub_cancel]
  push_cast
  have hkey : 1 + ((m : ℝ) + 1) * (a / u) ≤ ((m : ℝ) + 1 + 1) * w ^ (m + 1) := by
    push_cast at hber hau ⊢
    nlinarith [hber, hau]
  have humpos : (0 : ℝ) < u ^ m := by positivity
  have := mul_le_mul_of_nonneg_right hkey humpos.le
  calc u ^ (m + 1) + ((m : ℝ) + 1) * a * u ^ m
      = (1 + ((m : ℝ) + 1) * (a / u)) * u ^ m * u := by field_simp; ring
    _ ≤ (((m : ℝ) + 1 + 1) * w ^ (m + 1)) * u ^ m * u := by
        exact mul_le_mul_of_nonneg_right this hu.le
    _ = ((m : ℝ) + 1 + 1) * (w ^ (m + 1) * u ^ (m + 1)) := by ring
end Sendov
