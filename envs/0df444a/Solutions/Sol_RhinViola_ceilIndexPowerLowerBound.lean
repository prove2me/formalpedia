-- Prove2me | solution 1 for RhinViola.ceilIndexPowerLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T16:50:09.528892+00:00
-- url     : https://prove2.me/submissions/8a536d92-65a5-4d62-82f0-471bfeb8f1d5

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem solution
    (u c : ℝ) (q n : ℕ)
    (hu : 0 < u) (hc : 0 < c) (hq : 0 < q)
    (hn : (n : ℝ) < Real.log (2 * (q : ℝ)) / u + 1) :
    Real.exp (-c) * (2 : ℝ) ^ (-(c / u)) *
        (q : ℝ) ^ (-(c / u)) <
      Real.exp (-(c * (n : ℝ))) := by
  have hqR : 0 < (q : ℝ) := by
    exact_mod_cast hq
  have htwoq : 0 < (2 : ℝ) * (q : ℝ) := by
    positivity
  have hmul :
      c * (n : ℝ) <
        c * (Real.log (2 * (q : ℝ)) / u + 1) :=
    mul_lt_mul_of_pos_left hn hc
  have hneg :
      -(c * (Real.log (2 * (q : ℝ)) / u + 1)) <
        -(c * (n : ℝ)) :=
    neg_lt_neg hmul
  have hsplit :
      ((2 : ℝ) * (q : ℝ)) ^ (-(c / u)) =
        (2 : ℝ) ^ (-(c / u)) * (q : ℝ) ^ (-(c / u)) := by
    exact Real.mul_rpow (by positivity) hqR.le
  have hrpow :
      ((2 : ℝ) * (q : ℝ)) ^ (-(c / u)) =
        Real.exp (Real.log ((2 : ℝ) * (q : ℝ)) * (-(c / u))) := by
    exact Real.rpow_def_of_pos htwoq _
  calc
    Real.exp (-c) * (2 : ℝ) ^ (-(c / u)) *
          (q : ℝ) ^ (-(c / u)) =
        Real.exp (-c) * (((2 : ℝ) * (q : ℝ)) ^ (-(c / u))) := by
      rw [hsplit]
      ring
    _ = Real.exp (-c) *
          Real.exp (Real.log ((2 : ℝ) * (q : ℝ)) * (-(c / u))) := by
      rw [hrpow]
    _ = Real.exp
          (-c + Real.log ((2 : ℝ) * (q : ℝ)) * (-(c / u))) := by
      rw [Real.exp_add]
    _ = Real.exp
          (-(c * (Real.log (2 * (q : ℝ)) / u + 1))) := by
      congr 1
      ring
    _ < Real.exp (-(c * (n : ℝ))) :=
      Real.exp_lt_exp.mpr hneg
