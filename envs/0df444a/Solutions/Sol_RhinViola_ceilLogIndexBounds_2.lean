-- Prove2me | solution 2 for RhinViola.ceilLogIndexBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T11:51:28.399764+00:00
-- url     : https://prove2.me/submissions/26f8b092-5098-41af-80ea-8e97689b6fa5

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem solution
    (u : ℝ) (q : ℕ) (hu : 0 < u) (hq : 0 < q) :
    let n : ℕ := ⌈Real.log (2 * (q : ℝ)) / u⌉₊
    Real.log (2 * (q : ℝ)) / u ≤ (n : ℝ) ∧
      (n : ℝ) < Real.log (2 * (q : ℝ)) / u + 1 := by
  dsimp
  have hq_one_nat : 1 ≤ q := by
    exact hq
  have hq_one : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq_one_nat
  have htwoq : (1 : ℝ) ≤ 2 * (q : ℝ) := by
    nlinarith
  have hratio : 0 ≤ Real.log (2 * (q : ℝ)) / u := by
    exact div_nonneg (Real.log_nonneg htwoq) hu.le
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one hratio⟩
