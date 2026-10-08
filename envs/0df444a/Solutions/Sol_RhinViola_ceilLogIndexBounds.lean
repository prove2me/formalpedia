-- Prove2me | solution 1 for RhinViola.ceilLogIndexBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T11:47:50.619999+00:00
-- url     : https://prove2.me/submissions/bc694ee3-f45a-489d-9197-578adf2aac64

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem solution
    (u : ℝ) (q : ℕ) (hu : 0 < u) (hq : 0 < q) :
    let n : ℕ := ⌈Real.log (2 * (q : ℝ)) / u⌉₊
    Real.log (2 * (q : ℝ)) / u ≤ (n : ℝ) ∧
      (n : ℝ) < Real.log (2 * (q : ℝ)) / u + 1 := by
  dsimp
  have htwoq_nat : 1 ≤ 2 * q := by
    omega
  have htwoq : (1 : ℝ) ≤ 2 * (q : ℝ) := by
    exact_mod_cast htwoq_nat
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_nonneg htwoq
  have hratio : 0 ≤ Real.log (2 * (q : ℝ)) / u :=
    div_nonneg hlog hu.le
  constructor
  · exact Nat.le_ceil _
  · exact Nat.ceil_lt_add_one hratio
